import PEqualNP.MetaComplexity.Helpers.RepReads
import research.OneNotObservations

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.Helpers
open PEqualNP.MetaComplexity.RepReads

namespace OneNotCircuitReplacement

def signal {n : Nat} (pre : List Gate) (ins : List Nat) (x : Fin n → Bool) : Bool :=
  ((ins.map fun i => (wiresFrom pre (List.ofFn x)).getD i false).headD false)

def continuation {n : Nat} (pre post : List Gate) (out : Nat) (x : Fin n → Bool) (b : Bool) : Bool :=
  (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [b])).getD out false

theorem continuation_mono {n : Nat} (pre post : List Gate) (out : Nat)
    (hpost : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ x : Fin n → Bool, continuation pre post out x false = true →
      continuation pre post out x true = true := by
  intro x
  apply mono post (fun g hg => by simpa using hpost g hg) _ _ (by simp)
  intro i hi
  rw [getD_snoc] at hi ⊢
  by_cases he : i = (wiresFrom pre (List.ofFn x)).length
  · simp [he] at hi
  · simpa [he] using hi

theorem replace_by_true {n : Nat} (pre post : List Gate) (ins : List Nat) (out : Nat)
    (f : (Fin n → Bool) → Bool)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) = f x)
    (negative : ∀ x : Fin n → Bool, f x = false → signal pre ins x = false) :
    ∃ gates : List Gate,
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.length = (pre ++ ⟨GateOp.not, ins⟩ :: post).length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = f x := by
  have hcorrect : ∀ x : Fin n → Bool,
      continuation pre post out x (!signal pre ins x) = f x := by
    intro x
    have h := correct x
    change (wiresFrom (pre ++ ⟨GateOp.not, ins⟩ :: post) (List.ofFn x)).getD out false = f x at h
    rw [wiresFrom_append] at h
    exact h
  have replaced := replace_not_by_true f (signal pre ins) (continuation pre post out)
    (continuation_mono pre post out (fun g hg => (hpost g hg).1)) hcorrect negative
  refine ⟨pre ++ ⟨GateOp.and, []⟩ :: post, ?_, by simp, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hp | htail
    · exact hpre g hp
    · rcases List.mem_cons.mp htail with rfl | ht
      · simp
      · exact hpost g ht
  · intro x
    change (wiresFrom (pre ++ ⟨GateOp.and, []⟩ :: post) (List.ofFn x)).getD out false = f x
    rw [wiresFrom_append]
    exact replaced x

theorem replace_by_false {n : Nat} (pre post : List Gate) (ins : List Nat) (out : Nat)
    (f : (Fin n → Bool) → Bool)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpost : ∀ g ∈ post, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (correct : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, ins⟩ :: post, out⟩ (List.ofFn x) = f x)
    (positive : ∀ x : Fin n → Bool, f x = true → signal pre ins x = true) :
    ∃ gates : List Gate,
      (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.length = (pre ++ ⟨GateOp.not, ins⟩ :: post).length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates, out⟩ (List.ofFn x) = f x := by
  have hcorrect : ∀ x : Fin n → Bool,
      continuation pre post out x (!signal pre ins x) = f x := by
    intro x
    have h := correct x
    change (wiresFrom (pre ++ ⟨GateOp.not, ins⟩ :: post) (List.ofFn x)).getD out false = f x at h
    rw [wiresFrom_append] at h
    exact h
  have replaced := replace_not_by_false f (signal pre ins) (continuation pre post out)
    (continuation_mono pre post out (fun g hg => (hpost g hg).1)) hcorrect positive
  refine ⟨pre ++ ⟨GateOp.or, []⟩ :: post, ?_, by simp, ?_⟩
  · intro g hg
    rcases List.mem_append.mp hg with hp | htail
    · exact hpre g hp
    · rcases List.mem_cons.mp htail with rfl | ht
      · simp
      · exact hpost g ht
  · intro x
    change (wiresFrom (pre ++ ⟨GateOp.or, []⟩ :: post) (List.ofFn x)).getD out false = f x
    rw [wiresFrom_append]
    exact replaced x

end OneNotCircuitReplacement
