/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.ChernClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.Intersection

/- Lemma 42.41.4 (1): The intersection number of `d` invertible modules with a
dimension-`d` closed subscheme of a proper scheme over a field is the Chow degree
of their iterated first-Chern cap product with the associated cycle of the
subscheme. -/
@[stacks 0BFI]
#check (AlgebraicGeometry.Scheme.Modules.Intersection.number_eq_chowDegree_iteratedFirstChernClassCap :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (Z : X.left.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : Fin d → X.left.Modules) [∀ j : Fin d, Scheme.Modules.Invertible (L j)],
      number k X.hom Z hZdim L =
        (ChowGroup.degree X <|
          ChowGroup.iteratedFirstChernClassCap
              (fun _ : Spec (CommRingCat.of k) ↦ 0) X d L <|
            @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
              inferInstance (d : ℤ) <|
              @IdealSheafData.associatedCycle X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom) Z
                (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
                (d : ℤ) : ℚ))

/- Lemma 42.41.4 (2): For an ample invertible module, its degree on a
dimension-`d` closed subscheme is the Chow degree of its `d`-fold first-Chern
self-intersection with the associated cycle of the subscheme. -/
@[stacks 0BFI] #check (AlgebraicGeometry.Scheme.Modules.Intersection.degree_eq_chowDegree_firstChernClassPower :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (Z : X.left.IdealSheafData) {d : ℕ}
    (hZdim : topologicalKrullDim Z.subscheme = d)
    [HasExt (Sheaf (Opens.grothendieckTopology Z.subscheme.carrier) AddCommGrpCat.{u})]
    (L : X.left.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L],
      degree k X.hom L Z hZdim =
        (ChowGroup.degree X <|
          ChowGroup.iteratedFirstChernClassCap
              (fun _ : Spec (CommRingCat.of k) ↦ 0) X d (fun _ ↦ L) <|
            @chowClass X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
              inferInstance (d : ℤ) <|
              @IdealSheafData.associatedCycle X.left
                (LocallyOfFiniteType.isLocallyNoetherian X.hom) Z
                (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ 0))
                (d : ℤ) : ℚ))

end AlgebraicGeometry.Scheme.Modules.Intersection
