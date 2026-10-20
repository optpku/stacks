/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.InheritedFromHom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PropertyBeta
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Descent of properties of algebraic spaces

Property (β), decency, and reasonableness descend along quasi-compact étale
surjective morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Property (β) is inherited from the source of a quasi-compact étale
surjective morphism of algebraic spaces. -/
instance hasPropertyBeta_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@HasPropertyBeta S : ObjectProperty (AlgebraicSpace S))
      ((@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- Decency is inherited from the source of a quasi-compact étale surjective
morphism of algebraic spaces. -/
instance isDecent_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsDecent S : ObjectProperty (AlgebraicSpace S))
      ((@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- Reasonableness is inherited from the source of a quasi-compact étale
surjective morphism of algebraic spaces. -/
instance isReasonable_inheritedFromSource {S : Scheme.{u}} :
    InheritedFromSource (@IsReasonable S : ObjectProperty (AlgebraicSpace S))
      ((@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
        (@Surjective S : MorphismProperty (AlgebraicSpace S))) := sorry

/-- If `f : X ⟶ Y` is quasi-compact, étale, and surjective, and `X` has property
(β), then `Y` has property (β). -/
theorem HasPropertyBeta.of_quasiCompact_etale_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [Etale f] [Surjective f]
    [HasPropertyBeta X] : HasPropertyBeta Y :=
  ObjectProperty.of_hom_of_source
    (Q := (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S)))
    f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- If `f : X ⟶ Y` is quasi-compact, étale, and surjective, and `X` is decent, then
`Y` is decent. -/
theorem IsDecent.of_quasiCompact_etale_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [Etale f] [Surjective f]
    [IsDecent X] : IsDecent Y :=
  ObjectProperty.of_hom_of_source
    (Q := (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S)))
    f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- If `f : X ⟶ Y` is quasi-compact, étale, and surjective, and `X` is reasonable,
then `Y` is reasonable. -/
theorem IsReasonable.of_quasiCompact_etale_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [QuasiCompact f] [Etale f] [Surjective f]
    [IsReasonable X] : IsReasonable Y :=
  ObjectProperty.of_hom_of_source
    (Q := (@QuasiCompact S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Etale S : MorphismProperty (AlgebraicSpace S)) ⊓
      (@Surjective S : MorphismProperty (AlgebraicSpace S)))
    f ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end AlgebraicGeometry.AlgebraicSpace
