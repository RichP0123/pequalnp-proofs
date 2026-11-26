import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22873
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [8, 9]⟩,
  ⟨.or, [4, 7]⟩,
  ⟨.or, [5, 7]⟩,
  ⟨.or, [10, 12]⟩,
  ⟨.and, [0, 13]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.or, [10, 15]⟩,
  ⟨.and, [1, 16]⟩,
  ⟨.or, [5, 11]⟩,
  ⟨.and, [2, 18]⟩,
  ⟨.or, [5, 15]⟩,
  ⟨.and, [3, 20]⟩,
  ⟨.or, [14, 17]⟩,
  ⟨.or, [21, 22]⟩,
  ⟨.or, [19, 23]⟩], 24⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883514 : ℕ).testBit (6 * u.val + v.val)) 15 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22873

theorem PEqualNP.Outside.L_meta_22873 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (1883514 : ℕ).testBit (6 * u.val + v.val)) 15 := @PEqualNP.Outside.L_meta_22873.checked
