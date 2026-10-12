/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.Separable
public import ReasLib.AlgebraicGeometry.Curve.PurelyInseparable
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.IteratedRelative
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Variety
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Curve.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Scheme.Hom
open Scheme.Hom.IsNonconstant

universe u

namespace AlgebraicGeometry.Curve

/-- For a nonconstant morphism of proper regular curves in characteristic `p`,
an inseparable function-field extension of degree `p` identifies the target with
the relative Frobenius twist of the source, uniquely and compatibly with the map. -/
theorem uniqueIsoRelativeFrobeniusTargetOfInseparableDegree
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (h_finite : @FiniteFunctionFieldExtension _ _ f.left
      inferInstance inferInstance (isDominant_of_curves hf))
    (h_degree : @inducedFunctionFieldDegree _ _ f.left
      inferInstance inferInstance (isDominant_of_curves hf) = p)
    (h_inseparable :
      ¬@Algebra.IsSeparable Y.left.functionField X.left.functionField
        inferInstance inferInstance
        (@functionFieldAlgebra _ _ f.left inferInstance inferInstance
          (@map_genericPoint_eq_of_isDominant _ _ f.left
            inferInstance inferInstance (isDominant_of_curves hf)))) :
    ∃! e : Y ≅ @relativeFrobeniusTargetOver p inferInstance X.left
      (Spec (CommRingCat.of k))
        X.hom inferInstance,
      f ≫ e.hom = @relativeFrobeniusOver p inferInstance X.left
        (Spec (CommRingCat.of k))
        X.hom inferInstance := sorry

/-- A nonconstant morphism of proper regular curves with smooth source and a
purely inseparable function-field extension is uniquely an iterated relative
Frobenius, including its stage and target isomorphism. -/
theorem uniqueIteratedRelativeFrobeniusFactorization
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [Scheme.Regular X.left] [Scheme.Regular Y.left]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant)
    (h_pi : (f.left.functionFieldMap
      (@map_genericPoint_eq_of_isDominant _ _ f.left
        inferInstance inferInstance (isDominant_of_curves hf))).IsPurelyInseparable) :
    ∃! n : ℕ, ∃! e : Y ≅
      @Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n,
        f ≫ e.hom =
        @Scheme.iteratedRelativeFrobenius p inferInstance _ _ X.hom inferInstance n := sorry

/-- A nonconstant morphism of proper smooth curves in positive characteristic
factors through an iterated relative Frobenius with separable residual map. -/
theorem existsIteratedRelativeFrobeniusSeparableFactorization
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (X Y : SchemeOverField k) [Curve X] [Curve Y]
    [IsProper X.hom] [IsProper Y.hom] [Smooth X.hom] [Smooth Y.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant) :
    ∃ (n : ℕ) (g : @Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n ⟶ Y),
      ∃ (h_curve : Curve (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n)),
      ∃ (h_proper : IsProper (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n).hom),
      ∃ (h_smooth : Smooth (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n).hom),
        ∃ (h_nonconstant : g.left.IsNonconstant),
          @Scheme.iteratedRelativeFrobenius p inferInstance _ _ X.hom inferInstance n ≫ g = f ∧
            @Algebra.IsSeparable Y.left.functionField
              (@Scheme.pPowerTwist p inferInstance _ _ X.hom inferInstance n).left.functionField
              inferInstance inferInstance
              (@Scheme.Hom.functionFieldAlgebra _ _ g.left
                h_curve.toVariety.toIsIntegral inferInstance
                (@Scheme.Hom.map_genericPoint_eq_of_isDominant _ _ g.left
                  h_curve.toVariety.toIsIntegral inferInstance
                  (@isDominant_of_curves k _ _ _ h_curve inferInstance
                    g h_nonconstant))) := sorry

end AlgebraicGeometry.Curve
