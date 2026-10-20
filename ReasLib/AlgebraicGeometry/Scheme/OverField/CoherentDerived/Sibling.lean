/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.Sibling

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace

universe wA vD uD u

namespace AlgebraicGeometry.SchemeOverField

/-- Sibling exact triangulated functors from the bounded derived category of coherent
sheaves on a reduced projective scheme over a field are naturally isomorphic when
the first functor is fully faithful. -/
theorem isomorphic_of_areSiblings_of_isReduced_hProjective
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsReduced X.left] [HProjective X.hom]
    [Abelian (RingedSpace.Coh X.left.toRingedSpace)]
    [HasDerivedCategory.{wA} (RingedSpace.Coh X.left.toRingedSpace)]
    {𝒟 : Type uD} [Category.{vD} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
    [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    [IsTriangulated 𝒟]
    (F F' : DerivedCategory.Bounded (RingedSpace.Coh X.left.toRingedSpace) ⥤ 𝒟)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F.Full] [F.Faithful] (hsibling : Functor.areSiblings F F') :
    Nonempty (F ≅ F') := sorry

/-- Sibling exact triangulated functors from the bounded derived category of coherent
sheaves on a smooth proper scheme over a field are naturally isomorphic when
the first functor is fully faithful. -/
theorem isomorphic_of_areSiblings_of_smooth_proper
    {k : Type u} [Field k] (X : SchemeOverField k)
    [Smooth X.hom] [IsProper X.hom]
    [Abelian (RingedSpace.Coh X.left.toRingedSpace)]
    [HasDerivedCategory.{wA} (RingedSpace.Coh X.left.toRingedSpace)]
    {𝒟 : Type uD} [Category.{vD} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟]
    [HasShift 𝒟 ℤ] [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟]
    [IsTriangulated 𝒟]
    (F F' : DerivedCategory.Bounded (RingedSpace.Coh X.left.toRingedSpace) ⥤ 𝒟)
    [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]
    [F.Full] [F.Faithful] (hsibling : Functor.areSiblings F F') :
    Nonempty (F ≅ F') := sorry

end AlgebraicGeometry.SchemeOverField
