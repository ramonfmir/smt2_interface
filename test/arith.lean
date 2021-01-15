import smt2
import .test_tactics

lemma arith_simple :
    forall (x y : int),
        x < y →
        x + 1 < y + 1000 :=
begin
    intros, z3
end

lemma arith_wrong :
    forall (x y : int),
        x < y →
        x + 1 < y :=
begin
    intros, must_fail z3
end

lemma lt_trans_by_z3 :
    forall (x y z : int),
        x < y →
        y < z →
        x < z :=
begin
    intros, z3
end

lemma lt_float : ∀ (f1 f2 : native.float), 
    f1 + (1 : native.float) < f2 + (1 : native.float) → f1 < f2 :=
begin 
    intros, z3 "evox.log",
end
