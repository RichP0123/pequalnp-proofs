import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_22618
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
def witness : Circuit := ⟨[
  ⟨.or, [1, 3]⟩,
  ⟨.or, [5, 6]⟩,
  ⟨.or, [0, 1]⟩,
  ⟨.and, [4, 10]⟩,
  ⟨.or, [8, 11]⟩,
  ⟨.and, [12, 14]⟩,
  ⟨.or, [7, 9]⟩,
  ⟨.and, [0, 16]⟩,
  ⟨.or, [13, 15]⟩,
  ⟨.or, [17, 18]⟩,
  ⟨.or, [4, 11]⟩,
  ⟨.or, [7, 20]⟩,
  ⟨.and, [2, 21]⟩,
  ⟨.or, [19, 22]⟩], 23⟩

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

theorem checked : PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325118 : ℕ).testBit (6 * u.val + v.val)) 14 :=
  ⟨witness, monoTwoB_sound witness (by decide), by decide, by decide +kernel⟩
end PEqualNP.Outside.L_meta_22618

theorem PEqualNP.Outside.L_meta_22618 :
    PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) => (325118 : ℕ).testBit (6 * u.val + v.val)) 14 := @PEqualNP.Outside.L_meta_22618.checked
