import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import PEqualNP.Defs

open PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_18660
theorem checked : ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    let covers := fun T : Finset (Fin n) => ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T
    ¬G.Colorable 2 → (∀ v, (∃ w, G.Adj v w) → (G.neighborSet v).ncard = 3) → ∃ T, covers T ∧
    (∀ S, covers S → T.card ≤ S.card) ∧ (∀ u ∈ T, ∃ w ∉ T, G.Adj u w) ∧ (∃ u ∈ T, ∃ v ∈ T, G.Adj u v) ∧
    ∀ u ∈ T, ∀ v ∈ T, G.Adj u v →
      (G.edgeSet \ (G.incidenceSet u ∪ G.incidenceSet v)).ncard + ((T.erase u).erase v).card + 7 = G.edgeSet.ncard + T.card := by
  intro n G covers nonbip cubic
  classical
  let family := (Finset.univ : Finset (Finset (Fin n))).filter covers
  have all : (Finset.univ : Finset (Fin n)) ∈ family :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ _ _ => Or.inl (Finset.mem_univ _)⟩
  obtain ⟨T,hT,small⟩ := family.exists_min_image Finset.card ⟨_,all⟩
  have cov := (Finset.mem_filter.mp hT).2
  have minT (S) (h : covers S) := small S (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  have privateNbr (u) (hu : u ∈ T) : ∃ w ∉ T, G.Adj u w := by
    by_contra! no
    have smaller : covers (T.erase u) := by
      intro a b adj
      by_cases au : a = u
      · subst a
        exact Or.inr (Finset.mem_erase.mpr ⟨adj.ne.symm,by by_contra missing; exact no b missing adj⟩)
      by_cases bu : b = u
      · subst b
        exact Or.inl (Finset.mem_erase.mpr ⟨au,by by_contra missing; exact no a missing adj.symm⟩)
      exact (cov a b adj).imp (fun h => Finset.mem_erase.mpr ⟨au,h⟩) (fun h => Finset.mem_erase.mpr ⟨bu,h⟩)
    have bound := minT _ smaller
    have count := Finset.card_erase_add_one hu
    omega
  have interior : ∃ u ∈ T, ∃ v ∈ T, G.Adj u v := by
    by_contra! no
    apply nonbip
    refine ⟨SimpleGraph.Coloring.mk (fun v => if v ∈ T then (0 : Fin 2) else 1) ?_⟩
    intro a b adj
    by_cases ha : a ∈ T
    · have hb : b ∉ T := fun h => no a ha b h adj
      simp [ha,hb]
    · have hb := (cov a b adj).resolve_left ha
      simp [ha,hb]
  refine ⟨T,cov,minT,privateNbr,interior,?_⟩
  intro u hu v hv adj
  let I := G.incidenceSet u ∪ G.incidenceSet v
  have uc : (G.incidenceSet u).ncard=3 := by
    rw [G.ncard_incidenceSet,← G.ncard_neighborSet]
    exact cubic u ⟨v,adj⟩
  have vc : (G.incidenceSet v).ncard=3 := by
    rw [G.ncard_incidenceSet,← G.ncard_neighborSet]
    exact cubic v ⟨u,adj.symm⟩
  have sum := Set.ncard_union_add_ncard_inter (G.incidenceSet u) (G.incidenceSet v)
  rw [G.incidenceSet_inter_incidenceSet_of_adj adj,Set.ncard_singleton,uc,vc] at sum
  have isize : I.ncard = 5 := by change _ at sum; dsimp only [I]; omega
  have edges := Set.ncard_sdiff_add_ncard_of_subset
    (show I ⊆ G.edgeSet from Set.union_subset (G.incidenceSet_subset u) (G.incidenceSet_subset v))
  have cu := Finset.card_erase_add_one hu
  have cv := Finset.card_erase_add_one (Finset.mem_erase.mpr ⟨adj.ne.symm,hv⟩ : v ∈ T.erase u)
  change (G.edgeSet \ I).ncard + _ + 7 = _
  omega
end PEqualNP.Outside.L_meta_18660

theorem PEqualNP.Outside.L_meta_18660 :
    ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)),   have x3 : Finset (Fin x1) → Prop := fun (x3 : Finset (Fin x1)) => ∀ (x4 x5 : Fin x1), x2.Adj x4 x5 → x4 ∈ x3 ∨ x5 ∈ x3;   ¬x2.Colorable (2 : ℕ) → (∀ (x5 : Fin x1), (∃ (x6 : Fin x1), x2.Adj x5 x6) → (x2.neighborSet x5).ncard = (3 : ℕ)) → ∃ (x6 : Finset (Fin x1)), x3 x6 ∧ (∀ (x7 : Finset (Fin x1)), x3 x7 → x6.card ≤ x7.card) ∧ (∀ x7 ∈ x6, ∃ x9 ∉ x6, x2.Adj x7 x9) ∧ (∃ x7 ∈ x6, ∃ x8 ∈ x6, x2.Adj x7 x8) ∧ ∀ x7 ∈ x6, ∀ x9 ∈ x6, x2.Adj x7 x9 → (x2.edgeSet \ (x2.incidenceSet x7 ∪ x2.incidenceSet x9)).ncard + ((x6.erase x7).erase x9).card + (7 : ℕ) = x2.edgeSet.ncard + x6.card := @PEqualNP.Outside.L_meta_18660.checked
