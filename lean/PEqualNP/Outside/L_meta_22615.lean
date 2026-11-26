import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22615
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [4, 8]⟩,
  ⟨.or, [5, 9]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [7, 12]⟩,
  ⟨.and, [0, 13]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [10, 15]⟩,
  ⟨.and, [1, 16]⟩,
  ⟨.or, [7, 15]⟩,
  ⟨.and, [2, 18]⟩,
  ⟨.and, [3, 4]⟩,
  ⟨.or, [14, 17]⟩,
  ⟨.or, [19, 21]⟩,
  ⟨.or, [20, 22]⟩], 23⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321019 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22615

theorem PEqualNP.Outside.L_meta_22615 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (321019 : ℕ).testBit (6 * u.val + v.val)) 14 := @PEqualNP.Outside.L_meta_22615.checked
