/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.ClosedImmersion.FiniteType
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineKernel

/-!
# Rig-surjectivity of closed immersions
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FormalAlgebraicSpace
  AffineFormalAlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective

/-- A closed immersion between locally Noetherian formal algebraic spaces is
rig-surjective exactly when every étale affine test has base change induced by
a surjection of adic Noetherian rings whose kernel has a positive power
annihilated by an ideal of definition. -/
theorem iff_etaleAffine_kernel {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] :
    RigSurjective f ↔
      ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
        (v : V ⟶ Y) [Etale v],
        KernelKilledByPowIdealOfDefinition (pullback.snd f v) :=
  sorry

/-- If every étale morphism from an affine formal algebraic space to `Y` has
base change `pullback.snd f v` corresponding to a surjection of adic
Noetherian rings whose kernel has a positive power annihilated by an ideal of definition,
then the closed immersion `f` is rig-surjective. -/
theorem of_etaleAffine_kernel {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f]
    (h : ∀ {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
      (v : V ⟶ Y) [Etale v],
      KernelKilledByPowIdealOfDefinition (pullback.snd f v)) :
    RigSurjective f :=
  (iff_etaleAffine_kernel f).mpr h

/-- A rig-surjective closed immersion of locally Noetherian formal algebraic
spaces has the property that every étale morphism from an affine formal
algebraic space to `Y` has base change corresponding to a surjection of adic
Noetherian rings whose kernel has a positive power annihilated by an ideal of
definition. -/
theorem etaleAffine_kernel {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (f : X ⟶ Y)
    [ClosedImmersion f] [RigSurjective f]
    {V : (Over S)ᵒᵖ ⥤ Type u} [IsFormalAlgebraicSpace V] [IsAffine V]
    (v : V ⟶ Y) [Etale v] :
    KernelKilledByPowIdealOfDefinition (pullback.snd f v) :=
  (iff_etaleAffine_kernel f).mp inferInstance v

end AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective
