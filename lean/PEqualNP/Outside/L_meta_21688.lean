import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_21688
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [0, 1]⟩, ⟨.or, [5, 2]⟩, ⟨.and, [3, 1]⟩, ⟨.or, [4, 0]⟩, ⟨.or, [1, 8]⟩, ⟨.and, [2, 9]⟩, ⟨.or, [7, 10]⟩, ⟨.not, [11]⟩, ⟨.and, [6, 12]⟩], 13⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12891 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_21688

theorem PEqualNP.Outside.L_meta_21688 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 11 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12891 : ℕ).testBit (5 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_21688.checked
