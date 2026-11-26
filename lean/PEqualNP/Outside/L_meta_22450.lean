import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22450
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [5, 7]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.or, [9, 12]⟩,
  ⟨.and, [0, 13]⟩,
  ⟨.or, [10, 12]⟩,
  ⟨.and, [1, 15]⟩,
  ⟨.and, [2, 10]⟩,
  ⟨.and, [3, 11]⟩,
  ⟨.or, [14, 16]⟩,
  ⟨.or, [17, 19]⟩,
  ⟨.or, [18, 20]⟩,
  ⟨.or, [4, 21]⟩], 22⟩

def monoTwoB (C : Circuit) : Bool :=
  C.gates.all fun g =>
    (match g.op with | GateOp.and => true | GateOp.or => true | _ => false) &&
    Nat.ble g.inputs.length 2

theorem monoTwoB_sound (C : Circuit) (h : monoTwoB C = true) : Monotone2 C := by
  intro g hg
  have h1 := List.all_eq_true.1 h g hg
  simp only [Bool.and_eq_true, Nat.ble_eq] at h1
  refine ⟨?_, h1.2⟩
  cases hop : g.op <;> simp [hop] at h1 ⊢

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1882101 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22450

theorem PEqualNP.Outside.L_meta_22450 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1882101 : ℕ).testBit (6 * u.val + v.val)) 13 := @PEqualNP.Outside.L_meta_22450.checked
