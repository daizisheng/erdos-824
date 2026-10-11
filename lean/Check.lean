module

public import Erdos824

public section

/-! Run `lake env lean Check.lean` to see the statements, the definitions they use,
and the axioms of the main theorems. The hypothesis `SmoothSuccessorHyp` (smooth p+1) is
the one external input; it is not formalized here (see the paper). -/

#print Erdos824.h
#print Erdos824.SmoothSuccessorHyp
#print Erdos824.SmoothSuccessorHypWeak
#check @Erdos824.erdos824_of_smoothSuccessor
#check @Erdos824.erdos824_of_smoothSuccessorWeak
#print axioms Erdos824.erdos824_of_smoothSuccessor
#print axioms Erdos824.erdos824_of_smoothSuccessorWeak
