/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Smooth
import StacksCheckRecall

/-!
# Smooth curves

There are nested open substacks
`𝒞urves^{smooth, 1} ⊂ 𝒞urves^{smooth} ⊂ 𝒞urves`.
For a family of curves `f : X ⟶ S`, the classifying morphism factors through
`𝒞urves^{smooth}` precisely when `f` is smooth, and through
`𝒞urves^{smooth, 1}` precisely when `f` is smooth of relative dimension one.
Each condition is represented by an open of the base under arbitrary scheme
base change.

For a scheme `X` proper over a field `k` with dimension at most one, the
classifying morphism `Spec k ⟶ 𝒞urves` factors through `𝒞urves^{smooth}`
precisely when `X` is smooth over `k`, and through `𝒞urves^{smooth, 1}`
precisely when it is smooth over `k` and equidimensional of dimension one.
The unrestricted dimension criterion is that every irreducible component has
dimension one; for nonempty `X` this is equivalent to equidimensionality and
global dimension one.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.16.1. The smooth and smooth-relative-dimension-one conditions define
nested open substacks, with the family and field criteria stated above. -/
@[stacks 0DZZ] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_smooth_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      AlgebraicSpace.Smooth
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ↔
        Set.range T.hom ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_smoothDim1_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
    ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
      (AlgebraicSpace.Smooth
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) ∧
        RelativeDimension
          (pullbackAlongScheme.snd (hom P)
            (ofOverHomMk (σK := T.hom ≫ (base P).hom)
              (σL := (base P).hom) T.hom rfl)) 1) ↔
        Set.range T.hom ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smooth_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
    smooth S P ↔ AlgebraicSpace.Smooth (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothDim1_iff :
    ∀ {S : Scheme.{u}} (P : Obj S),
    smoothDim1 S P ↔
      AlgebraicSpace.Smooth (hom P) ∧ RelativeDimension (hom P) 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothDim1_le_smooth :
    ∀ {S : Scheme.{u}} (P : Obj S),
    smoothDim1 S P → smooth S P)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_smooth_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    smooth (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.smoothDim1_iff_scheme_components :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        ∀ Z : irreducibleComponents X.left, topologicalKrullDim Z = 1)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_smoothDim1_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    [Nonempty X.left] (hdim : topologicalKrullDim X.left ≤ 1),
    smoothDim1 (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      AlgebraicGeometry.Smooth X.hom ∧
        TopologicalSpace.EquidimensionalSpace X.left ∧
        topologicalKrullDim X.left = 1)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
