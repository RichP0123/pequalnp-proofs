import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_24669
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def witness : Circuit := ⟨[⟨.or, [3, 2]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [6, 7]⟩, ⟨.or, [4, 1]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [9, 10]⟩, ⟨.or, [8, 11]⟩, ⟨.not, [12]⟩], 13⟩
theorem fan : FanInTwo witness := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
theorem checked : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) :=
  ⟨witness, fan, by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_24669

theorem PEqualNP.Outside.L_meta_24669 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) = (34630321599 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := @PEqualNP.Outside.L_meta_24669.checked
