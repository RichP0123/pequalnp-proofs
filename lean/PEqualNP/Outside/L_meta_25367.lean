import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25367
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.not, [2]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [4, 2]⟩, ⟨.or, [3, 1]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [7, 13]⟩], 14⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4361531 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_25367

theorem PEqualNP.Outside.L_meta_25367 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (4361531 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_25367.checked
