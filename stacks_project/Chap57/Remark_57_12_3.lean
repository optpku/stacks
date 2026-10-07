module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import stacks_project.Chap57.Proposition_57_10_6
public import stacks_project.Chap57.Lemma_57_10_4_NegativeObjects

import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace

universe wA vD uD u

namespace AlgebraicGeometry.SchemeOverField

/-- The abelian category of coherent sheaves on a reduced projective scheme over a field
has enough negative objects in the sense used by Proposition 57.10.6. -/
theorem hasEnoughNegativeObjects_coh_of_isReduced_hProjective
    {k : Type u} [Field k] (X : SchemeOverField k)
    [IsReduced X.left] [HProjective X.hom]
    [Abelian (RingedSpace.Coh X.left.toRingedSpace)] :
    HasEnoughNegativeObjects (RingedSpace.Coh X.left.toRingedSpace) := sorry

/-- Remark 57.12.3 (1): if `F`, `F' : DerivedCategory.Bounded (RingedSpace.Coh X.left.toRingedSpace) ⥤ 𝒟`
are siblings, `F` is fully faithful, and `X` is reduced and projective over `k`, then
`Nonempty (F ≅ F')`. This follows from Proposition 57.10.6 via the argument in the
proof of Theorem 57.13.3. In general it is not known whether siblings are isomorphic,
including in the Fourier–Mukai existence setting of Lemma 57.12.2. -/
@[stacks 0G01]
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

/-- Remark 57.12.3 (2): if `F`, `F' : DerivedCategory.Bounded (RingedSpace.Coh X.left.toRingedSpace) ⥤ 𝒟`
are siblings, `F` is fully faithful, and `X` is smooth and proper over `k`, then
`Nonempty (F ≅ F')`, as shown in Noah. -/
@[stacks 0G01]
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
