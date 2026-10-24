import FlyCore

/-! The theorems the test suite checks rest on Lean's standard axioms alone. -/

#print axioms FlyCore.Ownership.eval_ok
#print axioms FlyCore.Ownership.program_ok
#print axioms FlyCore.Ownership.program_ok_sched
#print axioms FlyCore.Ownership.Concurrency.atomicEx_ok
#print axioms FlyCore.Ownership.Concurrency.chanEx_ok
#print axioms FlyCore.Ownership.Concurrency.mutexEx_ok
#print axioms FlyCore.Ownership.Check.infer_sound
#print axioms FlyCore.Ownership.Check.certified
