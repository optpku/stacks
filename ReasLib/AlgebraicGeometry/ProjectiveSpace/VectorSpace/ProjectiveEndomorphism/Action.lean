module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.ProjFromSections

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism

variable (k : Type u) [Field k]
variable (V : Type u) [AddCommGroup V] [Module k V]

/-- The projective scheme parametrizing projective endomorphisms of `V`. -/
abbrev parameterScheme : Scheme.{u} :=
  scheme k (Module.Dual k (Module.End k V))

/-- The product of the projective-endomorphism parameter scheme with `ℙ(V)`. -/
abbrev ambientScheme : Scheme.{u} :=
  parameterScheme k V ⨯ scheme k V

/-- The open locus where graded evaluation sections define a map to `ℙ(V)`. -/
noncomputable abbrev actionDomain
    (L : (ambientScheme k V).Modules) [Scheme.Modules.Invertible L]
    (evaluation : grading k V →+*ᵍ RingedSpace.GradedSections.grading L) :
    (ambientScheme k V).Opens :=
  Scheme.Modules.projSectionMapDomain (grading k V) L evaluation

/-- The projective-endomorphism action determined by canonical projective-section data. -/
noncomputable def action
    (L : (ambientScheme k V).Modules) [Scheme.Modules.Invertible L]
    (evaluation : grading k V →+*ᵍ RingedSpace.GradedSections.grading L)
    (P : ProjTwistPresentation (grading k V))
    (c : Scheme.Modules.ProjSectionMap (grading k V) L P evaluation)
    (hcanonical : c.IsCanonical) :
    (actionDomain k V L evaluation).toScheme ⟶ ambientScheme k V :=
  prod.lift
    ((actionDomain k V L evaluation).ι ≫
      (prod.fst : ambientScheme k V ⟶ parameterScheme k V))
    c.map

/-- The projective-endomorphism action preserves the parameter coordinate. -/
theorem action_fst
    (L : (ambientScheme k V).Modules) [Scheme.Modules.Invertible L]
    (evaluation : grading k V →+*ᵍ RingedSpace.GradedSections.grading L)
    (P : ProjTwistPresentation (grading k V))
    (c : Scheme.Modules.ProjSectionMap (grading k V) L P evaluation)
    (hcanonical : c.IsCanonical) :
    action k V L evaluation P c hcanonical ≫
        (prod.fst : ambientScheme k V ⟶ parameterScheme k V) =
      (actionDomain k V L evaluation).ι ≫
        (prod.fst : ambientScheme k V ⟶ parameterScheme k V) := sorry

/-- The second component of the projective-endomorphism action is the projective-section map. -/
theorem action_snd
    (L : (ambientScheme k V).Modules) [Scheme.Modules.Invertible L]
    (evaluation : grading k V →+*ᵍ RingedSpace.GradedSections.grading L)
    (P : ProjTwistPresentation (grading k V))
    (c : Scheme.Modules.ProjSectionMap (grading k V) L P evaluation)
    (hcanonical : c.IsCanonical) :
    action k V L evaluation P c hcanonical ≫
        (prod.snd : ambientScheme k V ⟶ scheme k V) =
      c.map := sorry

end AlgebraicGeometry.ProjectiveSpace.VectorSpace.ProjectiveEndomorphism
