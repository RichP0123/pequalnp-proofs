import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22850
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [6, 7]⟩,
  ⟨.or, [6, 8]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.or, [11, 12]⟩,
  ⟨.or, [9, 13]⟩,
  ⟨.and, [0, 14]⟩,
  ⟨.or, [4, 9]⟩,
  ⟨.or, [10, 16]⟩,
  ⟨.and, [1, 17]⟩,
  ⟨.or, [8, 10]⟩,
  ⟨.and, [2, 19]⟩,
  ⟨.and, [3, 12]⟩,
  ⟨.or, [15, 18]⟩,
  ⟨.or, [20, 22]⟩,
  ⟨.or, [21, 23]⟩], 24⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904055 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22850

theorem PEqualNP.Outside.L_meta_22850 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (904055 : ℕ).testBit (6 * u.val + v.val)) 15 := @PEqualNP.Outside.L_meta_22850.checked
