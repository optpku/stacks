/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Finite
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.OpenImmersion

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Etale

/-- The actual rank-one locus, independent of a marked fibre or a point law. -/
noncomputable def rankOneOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] : S.Opens :=
  ⟨{s | f.finrank s = 1}, f.isLocallyConstant_finrank.isOpen_fiber 1⟩

/-- Rank one on this exact locus follows from membership, without a marked-point law. -/
theorem rankOne_isIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] :
    IsIso (f ∣_ rankOneOpen f) := by
  apply (Scheme.Hom.isIso_iff_finrank_eq (f ∣_ rankOneOpen f)).2
  funext y
  change (f ∣_ rankOneOpen f).finrank y = 1
  rw [Scheme.Hom.finrank_of_isPullback
    (f ⁻¹ᵁ rankOneOpen f).ι (f ∣_ rankOneOpen f) f (rankOneOpen f).ι
    (AlgebraicGeometry.isPullback_morphismRestrict f (rankOneOpen f)).flip]
  exact y.property

/-- Both directions come from the proved native rank criterion on the actual locus. -/
noncomputable def rankOneIso
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] :
    (f ⁻¹ᵁ rankOneOpen f).toScheme ≅ (rankOneOpen f).toScheme :=
  @asIso _ _ _ _ (f ∣_ rankOneOpen f) (rankOne_isIso f)

/-- Concrete marked-point rank law. This law supplies only locus membership. -/
theorem rank_one_at_singleton_purelyInseparable
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) (x : X) (hxs : f x = s)
    (h_fiber : f ⁻¹' ({s} : Set S) = {x})
    (hκ : ((Scheme.residueFieldCongr hxs).inv ≫
      f.residueFieldMap x).hom.IsPurelyInseparable) :
    f.finrank s = 1 := by
  sorry

/-- A finite étale morphism with a singleton fibre and purely inseparable residue-field
extension restricts to an isomorphism over an open neighbourhood of the image point. -/
theorem exists_isIso_morphismRestrict
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f]
    (s : S) (x : X) (hxs : f x = s)
    (h_fiber : f ⁻¹' ({s} : Set S) = {x})
    (hκ : ((Scheme.residueFieldCongr hxs).inv ≫
      f.residueFieldMap x).hom.IsPurelyInseparable) :
    ∃ U : S.Opens, s ∈ U ∧ IsIso (f ∣_ U) := by
  refine ⟨rankOneOpen f, ?_, rankOne_isIso f⟩
  change f.finrank s = 1
  exact rank_one_at_singleton_purelyInseparable f s x hxs h_fiber hκ

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite étale morphism admits, étale-locally around any point of the target, a finite
pairwise disjoint clopen decomposition whose pieces map isomorphically to the neighbourhood. -/
theorem exists_clopen_decomposition_isIso_of_finite
    {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] [Etale f] (s : S) :
    ∃ (U : EtaleNeighborhood S s) (n : ℕ),
      let P := pullback f U.toEtale.hom
      let p := pullback.snd f U.toEtale.hom
      ∃ (V : Fin n → P.Opens)
        (_ : iSup V = ⊤)
        (_ : Pairwise (fun i j ↦ Disjoint (V i : Set P) (V j : Set P)))
        (_ : ∀ i, IsClopen (V i : Set P)),
        ∀ i, IsIso ((V i).ι ≫ p) := sorry

end AlgebraicGeometry.Scheme.Hom
