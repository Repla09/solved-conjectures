import SolvedConjectures

/-! Run `lake env lean Audit.lean` to print the statements and the axioms they use. -/

#check @SpiderL5.zero_rotatable
#check @SpiderGeneral.zero_rotatable
#print axioms SpiderL5.zero_rotatable
#print axioms SpiderGeneral.zero_rotatable
