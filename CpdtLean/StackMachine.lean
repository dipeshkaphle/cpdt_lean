namespace Types
inductive Binop: Type where
 | plus : Binop
 | times : Binop
inductive Exp : Type where
 | const : Nat → Exp
 | binop : Binop → Exp →  Exp → Exp
inductive Instr : Type where
 | iConst : Nat → Instr
 | iBinop : Binop → Instr

abbrev Prog := List Instr
abbrev Stack := List Nat
end Types

open Types

def binopDenote (b: Binop) :=
  match b with
  | Binop.plus =>  Nat.add
  | Binop.times => Nat.mul

def expDenote (e: Exp) : Nat :=
  match e with
  | Exp.const n => n
  | Exp.binop b e1 e2 => (binopDenote b) (expDenote e1) (expDenote e2)


#eval expDenote (Exp.const 3)

#eval expDenote (Exp.binop (Binop.plus) (Exp.const 10) (Exp.const 12))

-- Process an instruction given a stack
def instrDenote (i: Instr) (s: Stack) : Option Stack :=
  match i with
  | Instr.iConst n => Option.some (n::s)
  | Instr.iBinop b =>
    match s with
    | arg1::arg2::s' => Option.some ((binopDenote b) arg1 arg2 :: s')
    | _ => Option.none

-- Process a program given a stack
def progDenote (p: Prog) (s: Stack) : Option Stack :=
  match p with
  | List.nil => Option.some s
  | i::p' => (match (instrDenote i s) with
          | Option.some s' => progDenote p' s'
          | Option.none => Option.none)


def compile (e : Exp) : Prog :=
  match e with
  | Exp.const n => (Instr.iConst n)::[]
  | Exp.binop b e1 e2 => compile e2 ++ compile e1 ++ (Instr.iBinop b ::[])

@[simp] theorem nonEmptyProgramIfCompiled (e: Exp) : List.length (compile e) >= 1 :=  by
  induction e with
  | const a =>
    unfold compile
    simp
  | binop b e1 e2 =>
    unfold compile
    rw [List.length_append]
    rw [List.length_append]
    simp_arith
  done


theorem compile_correct' : ∀ e p s, progDenote (compile e ++ p) s = progDenote p (expDenote e :: s) := by
        intro e p s
        induction e generalizing p s with
        | const n =>
          unfold compile
          unfold expDenote
          conv => {
            lhs
            unfold progDenote
            simp
            unfold instrDenote
            simp
            rfl
          }
          done
        | binop b e1 e2 ih1 ih2 =>
            unfold compile
            unfold expDenote
            rw [List.append_assoc (compile e2)]
            rw [List.append_assoc (compile e2)]
            rw [ih2]
            rw [List.append_assoc (compile e1)]
            rw [ih1]
            simp
            conv => {
                lhs
                simp
                unfold progDenote
                simp
                unfold instrDenote
                simp
                rfl
            }


theorem compile_correct : ∀ (e: Exp) , progDenote (compile e) [] = Option.some ((expDenote e) :: []) := by {
  intro e
  rw [←List.append_nil (compile e)]
  rw [compile_correct']
  unfold progDenote
  rfl
}
