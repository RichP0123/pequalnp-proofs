import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22416
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [2, 3]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [6, 12]⟩,
  ⟨.and, [0, 4]⟩,
  ⟨.or, [9, 15]⟩,
  ⟨.or, [14, 16]⟩,
  ⟨.and, [2, 14]⟩,
  ⟨.or, [13, 18]⟩,
  ⟨.and, [11, 17]⟩,
  ⟨.and, [10, 19]⟩,
  ⟨.or, [20, 21]⟩], 22⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (917309 : ℕ).testBit (6 * u.val + v.val)) 13 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22416

theorem PEqualNP.Outside.L_meta_22416 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (917309 : ℕ).testBit (6 * u.val + v.val)) 13 := @PEqualNP.Outside.L_meta_22416.checked
