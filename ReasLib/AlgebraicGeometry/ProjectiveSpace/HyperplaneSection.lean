/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Relative.Twist
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hyperplane
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.InvertiblePower.Comparison
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Hyperplane-section sequences on projective space

This file defines the canonical multiplication and restriction maps associated to a section of
the tautological sheaf, packages them as a short complex, and states the existence of a section
giving a short exact complex for a coherent module over an infinite field.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {k : Type u} [Field k] {n : ℕ}
variable (P : ProjectiveSpaceOver (Spec (CommRingCat.of k)) n)

/-- Multiplication by a tautological section from the negative twist of a module to the module
itself. -/
noncomputable def hyperplaneSectionTwistMap
    (F : P.scheme.Modules) (s : P.tautologicalSheaf.sections) :
    P.twist F (-1) ⟶ F :=
  (ρ_ (P.twist F (-1))).inv ≫
    tensorHom (𝟙 (P.twist F (-1)))
      ((RingedSpace.unitIsoTensorUnit P.scheme.toRingedSpace).inv ≫
        P.tautologicalSheaf.unitHomEquiv.symm s) ≫
    (α_ F (@Scheme.Modules.tensorPowerInt P.scheme P.tautologicalSheaf
      P.tautologicalSheaf_isInvertible (-1))
      P.tautologicalSheaf).hom ≫
    tensorHom (𝟙 F)
      (@RingedSpace.InvertiblePower.rightEvaluationIso P.scheme.toRingedSpace
        P.tautologicalSheaf (Scheme.Modules.Invertible.ringedSpaceIsInvertible
          P.tautologicalSheaf_isInvertible)).hom ≫
    tensorHom (𝟙 F)
      (RingedSpace.unitIsoTensorUnit P.scheme.toRingedSpace).hom ≫
    (ρ_ F).hom

/-- The multiplication map is the composite of the unit comparison, the section morphism,
associativity, evaluation of the inverse tensor power, and the right unitor. -/
theorem hyperplaneSectionTwistMap_def
    (F : P.scheme.Modules) (s : P.tautologicalSheaf.sections) :
    hyperplaneSectionTwistMap P F s =
      (ρ_ (P.twist F (-1))).inv ≫
        tensorHom (𝟙 (P.twist F (-1)))
          ((RingedSpace.unitIsoTensorUnit P.scheme.toRingedSpace).inv ≫
            P.tautologicalSheaf.unitHomEquiv.symm s) ≫
        (α_ F (@Scheme.Modules.tensorPowerInt P.scheme P.tautologicalSheaf
          P.tautologicalSheaf_isInvertible (-1))
          P.tautologicalSheaf).hom ≫
        tensorHom (𝟙 F)
          (@RingedSpace.InvertiblePower.rightEvaluationIso P.scheme.toRingedSpace
            P.tautologicalSheaf (Scheme.Modules.Invertible.ringedSpaceIsInvertible
              P.tautologicalSheaf_isInvertible)).hom ≫
        tensorHom (𝟙 F)
          (RingedSpace.unitIsoTensorUnit P.scheme.toRingedSpace).hom ≫
        (ρ_ F).hom := sorry

namespace ProjectiveSpaceHyperplane

/-- A nonzero tautological section cuts out a hyperplane through its canonical zero-scheme
immersion. -/
theorem zeroSchemeι
    (s : P.tautologicalSheaf.sections)
    (hs : P.tautologicalSheaf.unitHomEquiv.symm s ≠
      (0 : (SheafOfModules.unit P.scheme.ringCatSheaf : P.scheme.Modules) ⟶
        P.tautologicalSheaf)) :
    ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s) := sorry

end ProjectiveSpaceHyperplane

/-- The unit map from a module to the pushforward of its pullback along the zero scheme of a
tautological section. -/
noncomputable def hyperplaneSectionRestrictionMap
    (F : P.scheme.Modules) (s : P.tautologicalSheaf.sections) :
    F ⟶ (Scheme.Modules.pushforward (P.tautologicalZeroSchemeι s)).obj
      ((Scheme.Modules.pullback (P.tautologicalZeroSchemeι s)).obj F) :=
  (Scheme.Modules.pullbackPushforwardAdjunction
    (P.tautologicalZeroSchemeι s)).unit.app F

/-- Multiplication by a tautological section followed by restriction to its zero scheme is
zero. -/
theorem hyperplaneSectionTwistMap_comp_restrictionMap
    (F : P.scheme.Modules) (s : P.tautologicalSheaf.sections) :
    hyperplaneSectionTwistMap P F s ≫ hyperplaneSectionRestrictionMap P F s = 0 := sorry

/-- The canonical three-term complex consisting of multiplication by a tautological section
followed by restriction to its zero scheme. -/
noncomputable def hyperplaneSectionSequence
    (F : P.scheme.Modules) (s : P.tautologicalSheaf.sections) :
    ShortComplex P.scheme.Modules :=
  ShortComplex.mk (hyperplaneSectionTwistMap P F s)
    (hyperplaneSectionRestrictionMap P F s)
    (hyperplaneSectionTwistMap_comp_restrictionMap P F s)

/-- The canonical hyperplane-section sequence of a module is short exact. -/
def hyperplaneSectionShortExactFor
    (F : P.scheme.Modules) (s : P.tautologicalSheaf.sections) : Prop :=
  (hyperplaneSectionSequence P F s).ShortExact

/-- On positive-dimensional projective space over an infinite field, every coherent module has
a nonzero tautological section whose zero scheme is a hyperplane and whose canonical section
complex is short exact. -/
theorem exists_nonzero_hyperplaneSection_shortExact_of_coherent
    [Infinite k] (hn : 1 ≤ n) (F : P.scheme.Modules) [F.IsCoherent] :
    ∃ s : P.tautologicalSheaf.sections,
      P.tautologicalSheaf.unitHomEquiv.symm s ≠
          (0 : (SheafOfModules.unit P.scheme.ringCatSheaf : P.scheme.Modules) ⟶
            P.tautologicalSheaf) ∧
        ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s) ∧
          (hyperplaneSectionSequence P F s).ShortExact := sorry

/-- On positive-dimensional projective space over an infinite field, a finite family of
coherent modules admits one common nonzero tautological section whose zero scheme is a
hyperplane and whose canonical section complex is short exact for every module in the family. -/
theorem exists_nonzero_hyperplaneSection_shortExact_of_coherent_finiteFamily
    [Infinite k] (hn : 1 ≤ n) (m : ℕ) (F : Fin m → P.scheme.Modules)
    (hcoh : ∀ j, (F j).IsCoherent) :
    ∃ s : P.tautologicalSheaf.sections,
      P.tautologicalSheaf.unitHomEquiv.symm s ≠
          (0 : (SheafOfModules.unit P.scheme.ringCatSheaf : P.scheme.Modules) ⟶
            P.tautologicalSheaf) ∧
        ProjectiveSpaceHyperplane P (P.tautologicalZeroSchemeι s) ∧
          ∀ j, hyperplaneSectionShortExactFor P (F j) s := sorry

end

end AlgebraicGeometry
