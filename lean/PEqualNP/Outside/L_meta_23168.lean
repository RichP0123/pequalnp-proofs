import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23168
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [6, 7]⟩,
  ⟨.or, [5, 8]⟩,
  ⟨.or, [9, 10]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [0, 11]⟩,
  ⟨.or, [4, 9]⟩,
  ⟨.and, [1, 14]⟩,
  ⟨.and, [2, 12]⟩,
  ⟨.or, [13, 15]⟩,
  ⟨.or, [16, 17]⟩,
  ⟨.or, [3, 18]⟩], 19⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_23168

theorem PEqualNP.Outside.L_meta_23168 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 6) => (30461 : ℕ).testBit (6 * u.val + v.val)) 11 := @PEqualNP.Outside.L_meta_23168.checked
