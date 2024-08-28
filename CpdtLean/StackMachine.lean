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


theorem compile_correct : ∀ (e: Exp) ,
progDenote (compile e) [] = Option.some ((expDenote e) :: []) := by {
  intro e
  rw [←List.append_nil (compile e)]
  rw [compile_correct']
  unfold progDenote
  rfl
}


namespace Types

-- nat or a bool is a type
inductive Typ where
  | nat
  | bool

-- types of binary operations, parameterized over the Typ
inductive TBinop: Typ -> Typ -> Typ -> Type where
  | tplus : TBinop .nat .nat .nat
  | ttimes : TBinop .nat .nat .nat
  | teq: forall t, TBinop t t .bool -- eq defined to be over any type
  | tlt : TBinop .nat .nat .bool

-- type of an expression
inductive TExp: Typ -> Type where
  | tnconst : Nat -> TExp .nat
  | tbconst : Bool -> TExp .bool
  | tbinop : forall t1 t2 t, TBinop t1 t2 t -> TExp t1 -> TExp t2 -> TExp t

-- type stack, just a stack maintaining the current type at the top?
abbrev TStack := List Typ

-- type of an instruction, parameterized over the old type stack and new type stack (TInstr: old_type_stack -> new_type_stack)
inductive TInstr : TStack -> TStack -> Type where
  | ti_nconst : forall s, Nat -> TInstr s (.nat::s)
  | ti_bconst : forall s, Bool -> TInstr s (.bool::s)
  | ti_binop : forall arg1 arg2 res s, TBinop arg1 arg2 res -> TInstr (arg1::arg2::s) (res::s)

-- type of a program, parameterized over the previous type stack and new type stack
inductive TProg : TStack -> TStack -> Type where
  -- program is unchanged
  | tnil : forall s, TProg s s
  -- takes an instruction(s1 -> s2), program(s2 -> s3), which results in a
  -- program (s1 -> s3). During interpretation, we process the instruction first
  -- and the rest of the program.
  | tcons : forall s1 s2 s3, TInstr s1 s2 -> TProg s2 s3 -> TProg s1 s3

end Types

-- convert our Typ to a Lean Type
def typeDenote (t: Typ) :=
    match t with
    | .nat => Nat
    | .bool => Bool


-- convert a TBinop to a Lean binary function
def tbinopDenote { arg1 arg2 res :Typ}
    (b: TBinop arg1 arg2 res) : typeDenote arg1 -> typeDenote arg2 -> typeDenote res :=
  match b with
  | .tplus => Nat.add
  | .ttimes => Nat.mul
  -- Cannot find a better way to do this,
  -- possibly refactor this
  | .tlt => (fun ( x y:Nat ) =>
        match ( Ord.compare x y ) with
        | .lt => true
        | _ => false
      )
  | .teq .nat => fun ( x y:Nat ) =>
        match ( Ord.compare x y ) with
        | .eq => true
        | _ => false
  | .teq .bool => fun ( x y:Bool) =>

        match ( Ord.compare x y ) with
        | .eq => true
        | _ => false

-- interpret a TExp
def texpDenote {t: Typ} (e: TExp t) : typeDenote t :=
  match e with
  | .tnconst n => n
  | .tbconst b => b
  | .tbinop _ _ _ b e1 e2 => (tbinopDenote b) (@texpDenote _ e1) (@texpDenote _ e2)



#check texpDenote
#eval texpDenote (.tnconst 20)
#eval texpDenote (.tbinop _ _ _ .tlt (.tnconst 10) (.tnconst 20) )
#eval texpDenote (.tbinop _ _ _ (.teq .nat) (.tnconst 20) (.tnconst 20) )
#eval texpDenote (.tbinop _ _ _ (.teq .nat) (.tnconst 21) (.tnconst 20) )


-- TStack(type stack) to Lean Types
def vstack (ts: TStack) : Type :=
    match ts with
    | List.nil => Unit
    | t::ts => typeDenote t × vstack ts

-- Interpret a TInstr. Takes in a TInstr, the value stack(based on type stack)
-- and reads a new value stack
def tinstrDenote { ts ts': TStack } (i: TInstr ts ts') : vstack ts -> vstack ts' :=
    match i with
    | TInstr.ti_nconst _ n => fun s => (n,s)
    | TInstr.ti_bconst _ b => fun s => (b,s)
    | TInstr.ti_binop _ _ _  _ binop => fun s =>
      let (arg1, (arg2, rest)) := s
      ((tbinopDenote binop arg1 arg2), rest)


-- Interpret a TProg. Takes in a TProg and then value stack and returns a new value stack
def tprogDenote {ts ts': TStack} (p: TProg ts ts') : vstack ts -> vstack ts' :=
    match p with
    -- Do nothing
    | TProg.tnil _ => fun s => s
    -- Interpret instr and then rest of the program
    | TProg.tcons _ _ _ instr prog' => fun s => tprogDenote prog' (tinstrDenote instr s)


def tconcat { ts ts' ts'': TStack } (p: TProg ts ts') : TProg ts' ts'' -> TProg ts ts'' :=
    match p with
    -- Do nothing
    | TProg.tnil _ => fun p => p
    -- drains the instructions of p and then adds instructions of p'
    | TProg.tcons _ _ _ instr rest => fun p' => TProg.tcons _ _ _ instr (tconcat rest p')

def tcompile { t: Typ } (e: TExp t) (ts: TStack) : TProg ts (t::ts) :=
    match e with
    | TExp.tbconst b => TProg.tcons _ _ _ (TInstr.ti_bconst _ b) ( .tnil _)
    | TExp.tnconst n => TProg.tcons _ _ _ (TInstr.ti_nconst _ n) (.tnil _)
    | TExp.tbinop _ _ _ op arg1 arg2 =>
    -- needs to be compiled in a way so that we have arg2, arg1 in stack and
    -- then apply the binary operation, hence this way ([arg2][arg1][<op>])
      tconcat (tcompile arg2 _)
              (tconcat (tcompile arg1 _)
                       (.tcons _ _ _ (.ti_binop _ _ _ _ op) (.tnil _)))

#eval tprogDenote (tcompile (.tnconst 42) .nil) Unit.unit

theorem tprogDenote_over_tconcat :
          forall ts ts' ts'' ( p1: TProg ts ts' ) ( p2: TProg ts' ts'' ) (vs: vstack ts),
          tprogDenote (tconcat p1 p2) vs = tprogDenote p2 (tprogDenote p1 vs) := by
    intro ts ts' ts'' p1
    induction p1 with
    | tnil => intro p2 vs; rfl
    | tcons _ _ _ instr prog IH =>
      intro p2 vs; unfold tconcat;
      conv => lhs;unfold tprogDenote; rw [IH]
      conv => rhs; arg 2; unfold tprogDenote;
      done

theorem tcompile_correct : forall t (e: TExp t) ts (s: vstack ts),
      tprogDenote (tcompile e ts) s  = (texpDenote e, s) := by
    intros t e ts s
    induction e generalizing ts s with
    | tnconst => unfold tcompile texpDenote; rfl
    | tbconst => unfold tcompile texpDenote; rfl
    | tbinop _ _ _ op e1 e2 IHe1 IHe2 =>
      unfold tcompile; unfold texpDenote;
      rw [tprogDenote_over_tconcat ]

      rw [tprogDenote_over_tconcat ]
      conv => lhs; unfold tprogDenote;  simp; rw [IHe2, IHe1]
      unfold tprogDenote
      conv => rhs;
      rfl
      done
