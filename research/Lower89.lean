import PEqualNP.MetaComplexity.Helpers.RepPath

open PEqualNP.Represents PEqualNP.MetaComplexity.RepReads

def cycleA : Fin 45 → Fin 45 → Bool := (fun a b : Fin 45 => decide (∃ i : Fin 15, ((a.val = i.val ∨ a.val = 15 + i.val) ∧ (b.val = (i.val + 1) % 15 ∨ b.val = 30 + i.val)) ∨ ((b.val = i.val ∨ b.val = 15 + i.val) ∧ (a.val = (i.val + 1) % 15 ∨ a.val = 30 + i.val))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem forcedLeft : (forcedL cycleA).card = 45 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem forcedRight : (forcedR cycleA).card = 45 := by
  decide +kernel

theorem lower89 (s : Nat) (h : RepSizeAtMost cycleA s) : 89 ≤ s := by
  have hread := reads_le cycleA h
  rw [forcedLeft, forcedRight] at hread
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem lower90 (s : Nat) (h : RepSizeAtMost cycleA s) : 90 ≤ s := by
  have hp := PEqualNP.MetaComplexity.RepPath.path 45 45 s cycleA 0 2 1 30
    (by decide) (by decide) (by decide) (by decide)
    (by exact ⟨0, by decide⟩) (by exact ⟨1, by decide⟩) h
  change (forcedL cycleA).card + (forcedR cycleA).card ≤ s at hp
  rw [forcedLeft, forcedRight] at hp
  omega
