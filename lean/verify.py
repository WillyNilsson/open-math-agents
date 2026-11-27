"""Generate and kernel-check a C1a step-function certificate for JSON weights.

Generic modules are unchanged from Will Kirschenman's optimization-certificates
commit c1ead4cfdde623a57d3a60f8b8abe56337095927. All generated files are local
to this verifier. Use --generic for the infrastructure/audit alone.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
WORK=HERE.parent
REF="c1ead4cfdde623a57d3a60f8b8abe56337095927"
FC_REF="9097e2f90e66d2f6244209cb1c07f7120d17ec53"
HASHES={"Analytic":"ade048f3ea467686bbc02140b3036a9efddbd882630347e9e3791feb87f005b8",
        "Kron":"1a76d034ac5cc2e5a8a420f19e3ed867253595a548a46e0ec4aef7b0ded4357c"}
STANDARD={"propext","Classical.choice","Quot.sound"}

def check(condition,message):
    if not condition:raise ValueError(message)

def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()

def capture(cmd,**kw):
    return subprocess.check_output(cmd,text=True,encoding="utf8",**kw).strip()

def changed(path,data):
    raw=data.encode("utf8")
    if not path.exists() or path.read_bytes()!=raw:path.write_bytes(raw)

def run_lean(lean,env,folder,source,build=True):
    tic=time.monotonic()
    name=Path(source).stem
    log=HERE/"build"/(name+".log")
    file=folder/source
    out=HERE/"build"/Path(source).with_suffix(".olean")
    out.parent.mkdir(parents=True,exist_ok=True)
    args=[str(lean),"-j1"]
    if name.startswith("Check") or name=="Main":
        # Keep the working set below half of the 32 GiB verification machine.
        args.extend(["-M","10000"])
    if build:args.extend(["-o",str(out)])
    args.append(source)
    print("Lean",source,flush=True)
    with log.open("wb") as stream:
        p=subprocess.run(args,cwd=folder,env=env,stdout=stream,stderr=subprocess.STDOUT)
    msg=log.read_text(encoding="utf8",errors="replace")
    if p.returncode or re.search(r"(^|\n).*\berror:",msg) or (
        re.search(r"declaration uses [`']sorry[`']",msg) and folder==HERE):
        raise RuntimeError(f"{source}: exit {p.returncode}\n{msg[-4500:]}")
    print("Checked",name,"in",round(time.monotonic()-tic,2),"seconds",flush=True)
    return msg

def audit(msg,names):
    results={}
    for name in names:
        matches=re.findall("'"+re.escape(name)+r"' depends on axioms: \[([^\]]*)\]",msg)
        check(len(matches)==1, f"Missing or duplicated axiom audit for {name}: {msg[-600:]}")
        ax={x.strip() for x in matches[0].split(",")}
        check(ax<=STANDARD,f"unexpected axiom in {name}: {ax-STANDARD}")
        results[name]=sorted(ax)
    return results

def generic(lean,env,fc):
    build=HERE/"build"; build.mkdir(exist_ok=True)
    local=HERE/"C1aUpper"
    for module,expected in HASHES.items():
        check(digest(local/(module+".lean"))==expected,f"generic {module} differs from pinned source")
    source="FormalConjectures/OptimizationConstants/1a.lean"
    check(capture(["git","hash-object","--path="+source,source],cwd=fc)==
          capture(["git","rev-parse","HEAD:"+source],cwd=fc),"upstream C1a module was modified")
    stamp=build/"generic.json"
    signature={"source":REF,"fc":FC_REF,"lean":capture([str(lean),"--version"],env=env),
               "import_hash":digest(fc/source),"hashes":HASHES}
    objs=[build/Path(f).with_suffix(".olean") for f in (source,"C1aUpper/Kron.lean","C1aUpper/Analytic.lean")]
    if not(stamp.exists() and json.loads(stamp.read_text())==signature and all(o.exists() for o in objs)):
        run_lean(lean,env,fc,source)
        run_lean(lean,env,HERE,"C1aUpper/Kron.lean")
        run_lean(lean,env,HERE,"C1aUpper/Analytic.lean")
        changed(stamp,json.dumps(signature,indent=2))
    gen_audit="C1aUpper/AuditGeneric.lean"
    names=["C1aUpper.kron_cert","C1aUpper.C1a_le_of_steps"]
    changed(HERE/gen_audit,"import C1aUpper.Analytic\n"+"".join("#print axioms "+n+"\n" for n in names))
    audit_log=build/"AuditGeneric.log"
    # Reuse the previous full audit only for unchanged compiled modules and audit commands.
    dependencies=[*objs,stamp,HERE/gen_audit]
    if audit_log.exists() and audit_log.stat().st_mtime_ns>=max(o.stat().st_mtime_ns for o in dependencies):
        result=audit(audit_log.read_text(encoding="utf8"),names)
    else:
        result=audit(run_lean(lean,env,HERE,gen_audit,False),names)
    print("Generic:",result,flush=True)
    return result

def read_heights(path,base):
    data=json.loads(path.read_bytes())
    if isinstance(data,list):
        heights=data
    elif "weights" in data:
        heights=data["weights"]
    elif base is not None and "base_scale" in data and "delta" in data:
        source=json.loads(base.read_bytes());scale=data["base_scale"]
        check(type(scale) is int and scale>0,"invalid base scale")
        heights=[h*scale for h in source["weights"]]
        indices=set()
        for i,change in data["delta"]:
            check(type(i) is int and 0<=i<len(heights) and i not in indices and type(change) is int,
                  "invalid or repeated delta index")
            heights[i]+=change
            indices.add(i)
    else:
        raise ValueError("expected weights array or --base for a delta witness")
    check(len(heights)>0 and all(type(x) is int and x>=0 for x in heights) and any(heights),
          "need nonempty, nonnegative integer heights of positive total mass")
    if isinstance(data,dict) and "N" in data:check(data["N"]==len(heights),"N disagrees with the weights")
    return heights,data

def coefficients(heights):
    width=(sum(h*h for h in heights).bit_length()+7)//8
    z=int.from_bytes(b"".join(h.to_bytes(width,"little") for h in heights),"little")
    raw=(z*z).to_bytes((2*len(heights)-1)*width,"little")
    return max(int.from_bytes(raw[p:p+width],"little") for p in range(0,len(raw),width))

def packing_bits(N,amax,M,S):
    return max((N*((1<<amax.bit_length())-1)**2).bit_length(),M.bit_length()+1,(S+1).bit_length())

def mk_data(heights,M,S):
    n=len(heights);amax=max(heights);bits=packing_bits(n,amax,M,S);chunk_size=256
    lines=["import C1aUpper.Kron","","namespace C1aUpper.Witness","",
           f"def N : ℕ := {n}",f"def B : ℕ := 2 ^ {bits}",f"def amax : ℕ := {amax}",
           f"def M : ℕ := {M}",f"def S : ℕ := {S}",f"def fuel : ℕ := {(2*n).bit_length()}",""]
    names=[]
    for i in range(0,n,chunk_size):
        value=0
        for h in reversed(heights[i:i+chunk_size]):value=(value<<bits)|h
        name=f"c{i//chunk_size}";names.append(name)
        lines.append(f"def {name} : ℕ := 0x{value:x}")
    # Algebraically the same low-chunk-first packing as the reference. A balanced
    # concatenation keeps total intermediate bit lengths logarithmic per digit.
    span=bits*chunk_size; level=0
    while len(names)>1:
        merged=[]
        for j in range(0,len(names),2):
            if j+1==len(names):
                merged.append(names[j]);continue
            name=f"p{level}_{j//2}"
            lines.append(f"def {name} : ℕ := {names[j]} + ({names[j+1]} <<< {span})")
            merged.append(name)
        span*=2;level+=1;names=merged
    lines.extend(["",f"def A : ℕ := {names[0]}","","end C1aUpper.Witness",""])
    return "\n".join(lines)

def compile_data(lean,env,datafile):
    build=HERE/"build";stamp=build/"data-input.json"
    signature={"source_sha256":digest(HERE/datafile),"kron_olean_sha256":digest(build/"C1aUpper/Kron.olean")}
    if stamp.exists() and json.loads(stamp.read_text())==signature and (build/"C1aUpper/Data.olean").exists():return
    run_lean(lean,env,HERE,datafile)
    changed(stamp,json.dumps(signature,indent=2))

def modular_sum_source():
    helper=(HERE/"reference/SumBound.lean").read_text(encoding="utf8")
    return helper.replace("import C1aUpper.Kron","import C1aUpper.CheckSize")+"""
namespace C1aUpper.Witness
open Finset
theorem hS : S ≤ ∑ i ∈ range N, digit B A i := by
  have hchecksum : S = A % (B - 1) := by decide +kernel
  rw [hchecksum]
  exact packed_mod_le_digit_sum B A N (by decide +kernel) hA
end C1aUpper.Witness
"""

RADIX_BRIDGE="""
/-- Use an explicit radix throughout to avoid reducing a large concrete packed
power merely to unify two ways of writing the small radix exponent. -/
theorem guarded_conv_with_radix {B k w N A M : ℕ}
    (hbase : B = 2 ^ (k + 1)) (hw : w ≤ k + 1)
    (hA : A < B ^ N)
    (hA_low : A &&& ((2 ^ w - 1) * unitMask B N) = A)
    (hnoCarry : N * (2 ^ w - 1) ^ 2 < B)
    (hY_low : (A * A) &&& ((2 ^ k - 1) * unitMask B (2 * N)) = A * A)
    (hM : M < 2 ^ k)
    (hguard : ((A * A) + (2 ^ k - 1 - M) * unitMask B (2 * N)) &&&
      ((2 ^ k) * unitMask B (2 * N)) = 0) :
    ∀ m < 2 * N, conv N (digit B A) m ≤ M := by
  subst B
  exact kron_guard_cert hw hA hA_low hnoCarry hY_low hM hguard
"""

def guard_module(lean,env,module,dependencies):
    build=HERE/"build";stamp=build/(module+"-inputs.json")
    signature={str(p.relative_to(HERE)):digest(p) for p in [HERE/(module+".lean"),*dependencies]}
    if stamp.exists() and json.loads(stamp.read_text())==signature and (build/(module+".olean")).exists():return
    run_lean(lean,env,HERE,module+".lean")
    changed(stamp,json.dumps(signature))

def verify_witness(path,lean,env,base,exact_receipt):
    started=time.monotonic()
    heights,data=read_heights(path,base)
    N=len(heights);S=sum(heights)
    if exact_receipt:
        hint=json.loads(exact_receipt.read_text(encoding="utf8"))
        check(hint["sha256"]==digest(path) and hint["N"]==N and int(hint["sum_a"])==S,"receipt does not match witness")
        M=int(hint["max_conv"])
        check(M>0,"invalid candidate peak in receipt")
    else:M=coefficients(heights)
    w=max(heights).bit_length();bits=packing_bits(N,max(heights),M,S);k=bits-1
    bound=Fraction(2*N*M,S*S)
    if isinstance(data,dict):
        for field,value in [("max_conv",M),("sum_a",S)]:
            if field in data:check(int(data[field])==value,f"{field} disagrees with raw weights")
        if "numerator" in data and "denominator" in data:
            check(bound==Fraction(int(data["numerator"]),int(data["denominator"])),"declared rational does not match raw weights")
    names=["C1aUpper.c1a_upper_verified"]
    datafile="C1aUpper/Data.lean"
    changed(HERE/datafile,mk_data(heights,M,S))
    # Keep the five same kernel-decided checks and generic proof as upstream.
    main_source=(HERE/"reference/Main262144.lean").read_text(encoding="utf8")
    main_source=main_source.split("/-- The witness also certifies")[0]+"end C1aUpper\n"
    main_source=main_source.replace("Data262144","Data").replace("D262144","Witness")
    main_source=main_source.replace("c1a_upper_262144","c1a_upper_verified")
    main_source=main_source.replace("262144-step",f"{N}-step")
    main_source=main_source.replace("24440309691768679463247675392",str(bound.numerator))
    main_source=main_source.replace("16264647129627086646956500225",str(bound.denominator))
    fact_groups={"CheckSize":["hA","hB"],"CheckHeights":["hamax"],"CheckSum":["hS"],"CheckSquare":["hM"]}
    for group,facts in fact_groups.items():
        checklines=[]
        for fact in facts:
            match=re.search(r"^theorem "+fact+r" : [^\n]+$",main_source,re.MULTILINE)
            check(match,f"missing template fact {fact}")
            checklines.append(match[0])
            main_source=main_source.replace(match[0]+"\n","")
        changed(HERE/f"C1aUpper/{group}.lean",
                "import C1aUpper.Data\n\nnamespace C1aUpper.Witness\n\n"+
                "\n".join(checklines)+"\n\nend C1aUpper.Witness\n")
    fact_groups["CheckGuard"]=[]
    main_source=main_source.replace("import C1aUpper.Data","import GuardKron\n"+"\n".join("import C1aUpper."+g for g in fact_groups))
    changed(HERE/"C1aUpper/CheckSum.lean",modular_sum_source())
    main_source=main_source.replace("le_trans hS (dsum_le B fuel A N)","hS")
    numeric={
       "CheckHeights":f"hA_low : A &&& ((2 ^ {w} - 1) * unitMask B N) = A",
       "CheckSquare":f"hY_low : (A * A) &&& ((2 ^ {k} - 1) * unitMask B (2 * N)) = A * A",
       "CheckGuard":f"hguard : ((A * A) + (2 ^ {k} - 1 - M) * unitMask B (2 * N)) &&& ((2 ^ {k}) * unitMask B (2 * N)) = 0",
    }
    for group,statement in numeric.items():
        changed(HERE/f"C1aUpper/{group}.lean","import Guard\nimport C1aUpper.Data\n\nnamespace C1aUpper.Witness\n\n"+
                f"theorem {statement} := by decide +kernel\n\nend C1aUpper.Witness\n")
    main_source=main_source.replace("namespace Witness",RADIX_BRIDGE+"\nnamespace Witness",1)
    main_source=main_source.replace("kron_cert B N amax M fuel fuel A hA hamax hB hM",
            f"guarded_conv_with_radix (B := B) (k := {k}) (w := {w}) (N := N) (A := A) (M := M) "+
            "(by decide +kernel) (by decide +kernel) hA hA_low (by decide +kernel) hY_low (by decide +kernel) hguard")
    mainfile="C1aUpper/Main.lean";auditfile="C1aUpper/Audit.lean"
    changed(HERE/mainfile,main_source)
    changed(HERE/auditfile,"import C1aUpper.Main\n#print axioms C1aUpper.c1a_upper_verified\n")
    build=HERE/"build"
    receipt=build/"witness.json"
    signature={"witness_sha256":digest(path),"base_sha256":digest(base) if base else None,
               "data_sha256":digest(HERE/datafile),"theorem_sha256":digest(HERE/mainfile),
               "generic_sha256":digest(build/"generic.json"),"guard_sha256":digest(HERE/"Guard.lean"),
               "guard_bridge_sha256":digest(HERE/"GuardKron.lean"),
               "fact_hashes":{g:digest(HERE/f"C1aUpper/{g}.lean") for g in fact_groups},
               "N":N,"sum":str(S),"max_conv":str(M),
               "numerator":str(bound.numerator),"denominator":str(bound.denominator)}
    complete=False
    if receipt.exists():
        prior=json.loads(receipt.read_text())
        complete=prior.get("status")=="verified" and prior.get("inputs")==signature and all(
            (build/f"C1aUpper/{name}.olean").exists() for name in ("Data","Main"))
    if not complete:
        # Old success receipts must not describe a newly generated, not-yet-checked file.
        changed(receipt,json.dumps({"inputs":signature,"status":"checking"},indent=2))
        compile_data(lean,env,datafile)
        guard_module(lean,env,"Guard",[build/"C1aUpper/Kron.olean"])
        guard_module(lean,env,"GuardKron",[build/"Guard.olean"])
        for group in fact_groups:
            module=f"C1aUpper/{group}.lean"
            factstamp=build/(group+".json")
            deps={"witness":signature["data_sha256"],"source":signature["fact_hashes"][group]}
            if not (factstamp.exists() and json.loads(factstamp.read_text())==deps and (build/f"C1aUpper/{group}.olean").exists()):
                run_lean(lean,env,HERE,module)
                changed(factstamp,json.dumps(deps))
        run_lean(lean,env,HERE,mainfile)
    report=audit(run_lean(lean,env,HERE,auditfile,False),names)
    changed(receipt,json.dumps({"inputs":signature,"status":"verified","axioms":report},indent=2)+"\n")
    print("Witness verified:",N,f"{bound.numerator}/{bound.denominator}",report,"elapsed",round(time.monotonic()-started,2),flush=True)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("witness",nargs="?",type=Path)
    p.add_argument("--generic",action="store_true")
    p.add_argument("--base",type=Path,help="Source weights when witness contains integer deltas")
    p.add_argument("--exact-receipt",type=Path,help="Optional SHA-256-bound external peak proposal; the kernel verifies the proposed bound")
    p.add_argument("--fc",type=Path,default=WORK/"fc")
    p.add_argument("--bin",type=Path,default=WORK/"elan/toolchains/leanprover--lean4---v4.33.1/bin")
    args=p.parse_args();fc=args.fc.resolve();binp=args.bin.resolve()
    check(capture(["git","rev-parse","HEAD"],cwd=fc)==FC_REF,"unexpected formal-conjectures revision")
    env=dict(os.environ);env["PATH"]=str(binp)+os.pathsep+env.get("PATH","")
    lean=binp/("lean.exe" if os.name=="nt" else "lean")
    lake=binp/("lake.exe" if os.name=="nt" else "lake")
    getpath=capture([str(lake),"env",sys.executable,"-c","import os;print(os.environ['LEAN_PATH'])"],cwd=fc,env=env)
    env["LEAN_PATH"]=str(HERE/"build")+os.pathsep+getpath
    generic(lean,env,fc)
    if not args.generic:
        check(args.witness is not None,"specify a JSON witness or --generic")
        verify_witness(args.witness.resolve(),lean,env,args.base.resolve() if args.base else None,
                       args.exact_receipt.resolve() if args.exact_receipt else None)

if __name__=="__main__":main()
