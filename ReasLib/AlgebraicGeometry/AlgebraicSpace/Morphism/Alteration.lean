/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Alteration
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GenericallyFinite.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Locus

/-!
# Alterations of integral algebraic spaces

An alteration is a proper dominant morphism of integral algebraic spaces that
is finite over some nonempty open subspace of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An alteration is a proper dominant morphism between integral algebraic
spaces that is finite over some nonempty open of the target. -/
class IsAlteration {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsIntegral X] (f : Y ⟶ X) : Prop
    extends Proper f, Dominant f where
  /-- The alteration is finite over some nonempty open subspace of the target. -/
  exists_nonempty_open_isFinite :
    ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧ IsFinite (pullback.snd f U.ι)

/-- Over integral source and target algebraic spaces, a morphism is an
alteration if and only if it is proper, dominant, and finite over some
nonempty open of the target. -/
theorem isAlteration_iff {S : Scheme.{u}} {Y X : AlgebraicSpace S}
    [IsIntegral Y] [IsIntegral X] (f : Y ⟶ X) :
    IsAlteration f ↔
      Proper f ∧ Dominant f ∧
        ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧
          IsFinite (pullback.snd f U.ι) := by
  constructor
  · intro h
    exact ⟨h.toProper, h.toDominant, h.exists_nonempty_open_isFinite⟩
  · rintro ⟨hp, hd, hf⟩
    exact { toProper := hp, toDominant := hd, exists_nonempty_open_isFinite := hf }

/-- The identity morphism of an integral algebraic space is an alteration. -/
instance instIsAlteration_id {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsIntegral X] : IsAlteration (𝟙 X) := by
  refine {
    toProper := inferInstance
    toDominant := inferInstance
    exists_nonempty_open_isFinite := ?_ }
  obtain ⟨x, _⟩ := exists_mem_genericPoints X
  refine ⟨OpenSubspace.id X, ?_, ?_⟩
  · exact ⟨x, x, by simp [OpenSubspace.id, OpenSubspace.ofι, Points.map_id]⟩
  · change IsFinite (pullback.snd (𝟙 X) (𝟙 X))
    infer_instance

/-- An alteration of schemes over `S` induces an alteration of the associated
algebraic spaces. -/
instance instIsAlteration_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (f : U ⟶ V) [AlgebraicGeometry.IsIntegral U.left]
    [AlgebraicGeometry.IsIntegral V.left]
    [AlgebraicGeometry.IsAlteration f.left] :
    IsAlteration (ofOverMap f) :=
  sorry

private theorem isGenericPoint_univ_of_mem_genericPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsIrreducible X]
    {x : Points X} (hx : x ∈ genericPoints X) : IsGenericPoint x Set.univ := by
  have hτ : IsPointsTopology X (inferInstance : TopologicalSpace (Points X)) := by
    intro U p hp hs
    exact (Points.isOpenQuotientMap_mapOfOver p hp hs).isQuotientMap
  letI := IsIrreducible.irreducibleSpace (X := X) _ hτ
  change closure {x} ∈ irreducibleComponents (Points X) at hx
  change closure {x} = Set.univ
  simpa only [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] using hx

/-- A proper dominant morphism of integral algebraic spaces is an alteration
if and only if it is finite over some nonempty affine open of the target. -/
theorem isAlteration_iff_exists_isAffine_isFinite {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Proper f] [Dominant f] :
    IsAlteration f ↔
      ∃ V : OpenSubspace Y,
        V.pointsSet.Nonempty ∧ IsAffine V.X ∧
          IsFinite (pullback.snd f V.ι) := by
  constructor
  · intro h
    obtain ⟨U, hU, hfin⟩ := h.exists_nonempty_open_isFinite
    obtain ⟨x, hx⟩ := exists_mem_genericPoints X
    have hy : Points.map f x ∈ U.pointsSet := by
      have hg := isGenericPoint_univ_of_mem_genericPoints
        (map_mem_genericPoints_of_isDominant f hx)
      apply (hg.mem_open_set_iff U.isOpen_pointsSet).2
      simpa only [Set.univ_inter] using hU
    obtain ⟨u, hu⟩ := hy
    obtain ⟨z, hz, _⟩ := Points.exists_of_map_eq
      (IsPullback.of_hasPullback f U.ι) x u hu.symm
    letI := hfin
    have hq : QuasiFiniteAt (pullback.snd f U.ι) z := by
      refine ⟨_, 𝟙 _, inferInstance, ⟨z, ?_⟩, ?_⟩
      · simp [Points.map_id]
      · simpa only [Category.id_comp] using
          (QuasiFinite.of_isFinite (pullback.snd f U.ι)).locallyQuasiFinite
    have hqx := (quasiFiniteAt_iff_of_isPullback
      (pullback.fst f U.ι) (pullback.snd f U.ι) f U.ι
      (IsPullback.of_hasPullback f U.ι) z).1 hq
    rw [hz] at hqx
    exact (genericallyFinite_tfae_of_quasiCompact_or_separated f hx
      (Or.inl inferInstance)).out 3 5 |>.mp hqx
  · rintro ⟨V, hV, _, hfin⟩
    exact (isAlteration_iff f).2 ⟨inferInstance, inferInstance, V, hV, hfin⟩

/-- For a proper dominant morphism of integral algebraic spaces, being an
alteration is equivalent to the generic residue-field, finite affine restriction,
quasi-finiteness, singleton generic-fibre, and finite affine target-open conditions. -/
theorem isAlteration_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [Proper f] [Dominant f]
    {x : Points X} (hx : x ∈ genericPoints X) :
    List.TFAE
      [ IsAlteration f
      , residueFieldTrdegAt f x = 0
      , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
      , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
          U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
            IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
      , QuasiFiniteAt f x
      , Points.map f ⁻¹' {Points.map f x} = {x}
      , ∃ V : OpenSubspace Y,
          V.pointsSet.Nonempty ∧ IsAffine V.X ∧
            IsFinite (pullback.snd f V.ι) ] := by
  have hgf := genericallyFinite_tfae_of_quasiCompact_or_separated f hx
    (Or.inl inferInstance)
  exact List.tfae_cons_cons.mpr
    ⟨(isAlteration_iff_exists_isAffine_isFinite f).trans (hgf.out 5 0), hgf⟩

/-- A proper dominant morphism of integral algebraic spaces is an alteration
if and only if the residue-field transcendence degree at a generic point is
`0`. -/
theorem isAlteration_iff_residueFieldTrdegAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [Proper f] [Dominant f] {x : Points X} (hx : x ∈ genericPoints X) :
    IsAlteration f ↔ residueFieldTrdegAt f x = 0 :=
  (isAlteration_tfae f hx).out 0 1

/-- A proper surjective morphism of algebraic spaces onto an integral target
restricts to an alteration along some integral closed subspace of its source. -/
theorem exists_integralClosedSubspace_isAlteration
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsIntegral Y]
    (f : X ⟶ Y) [Proper f] [Surjective f] :
    ∃ (X' : ClosedSubspace X) (hX' : IsIntegral X'.X),
      IsAlteration (X'.ι ≫ f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
