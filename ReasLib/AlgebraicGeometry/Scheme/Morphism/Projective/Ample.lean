module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.ProjectiveSpace
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Tensor
import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.Power
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Constructors
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Cover
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Factorization

/-!
# Projective and quasi-projective morphisms with ample modules

This module relates proper morphisms carrying relatively ample modules to local projectivity and
compares projective and quasi-projective morphisms over bases admitting ample invertible modules
with their H-projective variants, geometric ampleness criteria, and relative-Proj presentations.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A proper scheme morphism admitting a relatively ample module is locally projective. -/
theorem locallyProjective_of_isProper_exists_relativelyAmple
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (h : ∃ L : X.Modules, RelativelyAmple f L) :
    LocallyProjective f := sorry

/-- A projective morphism to a scheme admitting an ample invertible module is H-projective. -/
theorem Projective.toHProjective_of_hasAmpleInvertibleModule
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : Projective f)
    (hS : Scheme.Modules.HasAmpleInvertibleModule S) :
    HProjective f := sorry

/-- A quasi-projective morphism to a scheme admitting an ample invertible module is
H-quasi-projective. -/
theorem QuasiProjective.toHQuasiProjective_of_hasAmpleInvertibleModule
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : QuasiProjective f)
    (hS : Scheme.Modules.HasAmpleInvertibleModule S) :
    HQuasiProjective f := sorry

namespace QuasiProjective

/-- For a morphism to a scheme admitting an ample invertible module, quasi-projectivity,
H-quasi-projectivity, projective compactifiability, finite type with an ample invertible module
on the source, and finite type with a relatively very ample module are equivalent. -/
theorem tfae_of_hasAmpleInvertibleModule
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : Scheme.Modules.HasAmpleInvertibleModule S) :
    List.TFAE [
      QuasiProjective f,
      HQuasiProjective f,
      ∃ (X' : Scheme.{u}) (i : X ⟶ X') (g : X' ⟶ S)
        (_ : QuasiCompact i) (_ : IsOpenImmersion i) (_ : Projective g),
        i ≫ g = f,
      Scheme.Hom.FiniteType f ∧ Scheme.Modules.HasAmpleInvertibleModule X,
      Scheme.Hom.FiniteType f ∧ ∃ L : X.Modules, RelativelyVeryAmple f L] := sorry

end QuasiProjective

namespace Projective

/-- For a morphism to a scheme admitting an ample invertible module, projectivity,
H-projectivity, proper quasi-projectivity and H-quasi-projectivity, properness with absolute or
relative ampleness, and a finite degree-one-generated relative-Proj presentation are equivalent.
-/
theorem tfae_of_hasAmpleInvertibleModule
    {X S : Scheme.{u}} (f : X ⟶ S)
    (hS : Scheme.Modules.HasAmpleInvertibleModule S) :
    List.TFAE [
      Projective f,
      HProjective f,
      QuasiProjective f ∧ IsProper f,
      HQuasiProjective f ∧ IsProper f,
      IsProper f ∧ Scheme.Modules.HasAmpleInvertibleModule X,
      IsProper f ∧ ∃ L : X.Modules, RelativelyAmple f L,
      IsProper f ∧ ∃ L : X.Modules, RelativelyVeryAmple f L,
      ∃ P : Scheme.Hom.RelativeProjPresentation f,
        P.GeneratedByDegreeOneFinite ∧ (P.degreePiece 1).IsFiniteType] := sorry

end Projective

end AlgebraicGeometry
