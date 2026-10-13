import Mathlib.Combinatorics.SimpleGraph.Finite

namespace NCop

/-- An undirected edge of the complete graph on `Fin m`. We reuse Mathlib's
edge representation for simple graphs, namely non-diagonal unordered pairs. -/
abbrev Edge (m : Nat) := (⊤ : SimpleGraph (Fin m)).edgeSet

namespace Edge

variable {m : Nat}

def incident (e : Edge m) (u v : Fin m) : Prop :=
  u ∈ (e : Sym2 (Fin m)) ∧ v ∈ (e : Sym2 (Fin m)) ∧ u ≠ v

def touches (e : Edge m) (v : Fin m) : Prop :=
  v ∈ (e : Sym2 (Fin m))

def between (u v : Fin m) (h : u ≠ v) : Edge m where
  val := s(u, v)
  property := by
    rw [SimpleGraph.mem_edgeSet]
    simpa using h

@[simp] theorem touches_between_left {u v : Fin m} (h : u ≠ v) :
    touches (between u v h) u := by
  simp [touches, between]

@[simp] theorem touches_between_right {u v : Fin m} (h : u ≠ v) :
    touches (between u v h) v := by
  simp [touches, between]

@[simp] theorem incident_between {u v : Fin m} (h : u ≠ v) :
    incident (between u v h) u v := by
  simp [incident, between, h]

end Edge

/-- A board records which edges Maker has claimed and which edges Breaker has
deleted. `Valid` states that the two sets are disjoint. -/
structure Board (m : Nat) where
  maker : Edge m -> Prop
  breaker : Edge m -> Prop

namespace Board

variable {m : Nat}

def Valid (B : Board m) : Prop :=
  ∀ e, ¬ (B.maker e ∧ B.breaker e)

def free (B : Board m) (e : Edge m) : Prop :=
  ¬ B.maker e ∧ ¬ B.breaker e

def empty (m : Nat) : Board m where
  maker := fun _ => False
  breaker := fun _ => False

def addMaker (B : Board m) (e0 : Edge m) : Board m where
  maker := fun e => B.maker e ∨ e = e0
  breaker := B.breaker

def addBreakerSet (B : Board m) (D : Edge m -> Prop) : Board m where
  maker := B.maker
  breaker := fun e => B.breaker e ∨ D e

def noFreeEdges (B : Board m) : Prop :=
  ∀ e, ¬ B.free e

def makerAdjacent (B : Board m) (u v : Fin m) : Prop :=
  ∃ e, B.maker e ∧ Edge.incident e u v

end Board

/-- The two distinguished vertices. -/
structure Terminals (m : Nat) where
  s : Fin m
  t : Fin m
  distinct : s ≠ t

/-- Reachability in Maker's claimed graph. -/
inductive MakerReach {m : Nat} (B : Board m) : Fin m -> Fin m -> Prop where
  | refl (v : Fin m) : MakerReach B v v
  | step {u v w : Fin m} :
      B.makerAdjacent u v -> MakerReach B v w -> MakerReach B u w

def MakerHasPath {m : Nat} (T : Terminals m) (B : Board m) : Prop :=
  MakerReach B T.s T.t

/-- `AtMost k P` means the predicate `P` is supported on a list of length at
most `k`. This avoids committing to a finite-set representation in the trusted
game layer. -/
def AtMost {alpha : Type u} (k : Nat) (P : alpha -> Prop) : Prop :=
  ∃ xs : List alpha, (∀ x, P x -> x ∈ xs) ∧ xs.length <= k

def LegalBreakerMove {m : Nat} (n : Nat) (B : Board m)
    (D : Edge m -> Prop) : Prop :=
  B.Valid ∧ (∀ e, D e -> B.free e) ∧ AtMost n D

def LegalMakerMove {m : Nat} (B : Board m) (e : Edge m) : Prop :=
  B.Valid ∧ B.free e

inductive BreakerTurn where
  | beforeBreaker
  | beforeMaker

/-- Breaker can force a win from a board, with the turn indicating whether the
state is before Breaker's deletion move or before Maker's claim move. -/
inductive BreakerCanForce {m : Nat} (T : Terminals m) (n : Nat) :
    BreakerTurn -> Board m -> Prop where
  | doneBefore {B : Board m} :
      B.Valid ->
      ¬ MakerHasPath T B ->
      B.noFreeEdges ->
      BreakerCanForce T n BreakerTurn.beforeBreaker B
  | delete {B : Board m} {D : Edge m -> Prop} :
      B.Valid ->
      ¬ MakerHasPath T B ->
      LegalBreakerMove n B D ->
      BreakerCanForce T n BreakerTurn.beforeMaker (B.addBreakerSet D) ->
      BreakerCanForce T n BreakerTurn.beforeBreaker B
  | doneAfter {B : Board m} :
      B.Valid ->
      ¬ MakerHasPath T B ->
      B.noFreeEdges ->
      BreakerCanForce T n BreakerTurn.beforeMaker B
  | reply {B : Board m} :
      B.Valid ->
      ¬ MakerHasPath T B ->
      (∀ e, LegalMakerMove B e ->
        BreakerCanForce T n BreakerTurn.beforeBreaker (B.addMaker e)) ->
      BreakerCanForce T n BreakerTurn.beforeMaker B

/-- Breaker can force a win from a board before Breaker's move. -/
abbrev BreakerWinFrom {m : Nat} (T : Terminals m) (n : Nat) (B : Board m) : Prop :=
  BreakerCanForce T n BreakerTurn.beforeBreaker B

/-- Breaker can force a win from a board after Breaker's move and before
Maker's reply. -/
abbrev BreakerWinAfter {m : Nat} (T : Terminals m) (n : Nat) (B : Board m) : Prop :=
  BreakerCanForce T n BreakerTurn.beforeMaker B

inductive MakerTurn where
  | beforeBreaker
  | beforeMaker

/-- Maker can force a win from a board, with the turn indicating whether the
state is before Breaker's deletion move or before Maker's claim move. -/
inductive MakerCanForce {m : Nat} (T : Terminals m) (n : Nat) :
    MakerTurn -> Board m -> Prop where
  | doneBefore {B : Board m} :
      MakerHasPath T B ->
      MakerCanForce T n MakerTurn.beforeBreaker B
  | surviveDelete {B : Board m} :
      B.Valid ->
      ¬ MakerHasPath T B ->
      (∀ D, LegalBreakerMove n B D ->
        MakerCanForce T n MakerTurn.beforeMaker (B.addBreakerSet D)) ->
      MakerCanForce T n MakerTurn.beforeBreaker B
  | doneAfter {B : Board m} :
      MakerHasPath T B ->
      MakerCanForce T n MakerTurn.beforeMaker B
  | claim {B : Board m} {e : Edge m} :
      B.Valid ->
      ¬ MakerHasPath T B ->
      LegalMakerMove B e ->
      MakerCanForce T n MakerTurn.beforeBreaker (B.addMaker e) ->
      MakerCanForce T n MakerTurn.beforeMaker B

/-- Maker can force a win from a board before Breaker's move. -/
abbrev MakerWinFrom {m : Nat} (T : Terminals m) (n : Nat) (B : Board m) : Prop :=
  MakerCanForce T n MakerTurn.beforeBreaker B

/-- Maker can force a win from a board after Breaker's move and before
Maker's reply. -/
abbrev MakerWinAfter {m : Nat} (T : Terminals m) (n : Nat) (B : Board m) : Prop :=
  MakerCanForce T n MakerTurn.beforeMaker B

/-- Breaker wins the original two-terminal game on `K_m` with bias `n`.
The terminal pair is quantified universally; for complete graphs this is
equivalent to fixing any pair, but avoids baking a particular pair into the
definition. -/
def BreakerWins (m n : Nat) : Prop :=
  ∀ T : Terminals m, BreakerWinFrom T n (Board.empty m)

/-- Maker wins the original two-terminal game on `K_m` with bias `n`. -/
def MakerWins (m n : Nat) : Prop :=
  ∀ T : Terminals m, MakerWinFrom T n (Board.empty m)

end NCop
