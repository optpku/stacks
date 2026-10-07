module

public import Mathlib.AlgebraicGeometry.Sites.Representability
public import ReasLib.AlgebraicGeometry.Scheme.RelativeProj.Degree.Transition

/-!
# Relative projective-spectrum functors

This module packages a relative projective-spectrum functor together with its
representable positive-degree open charts, their canonical quadruple classifications,
and a covering map compatible with the specified degree transitions.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {S : Scheme.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf)

/-- A relative projective-spectrum functor together with its representable
positive-degree open charts and their joint Zariski cover. -/
class RelativeProjFunctor
    (S : Scheme.{u}) (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) where
  /-- The graded algebra is quasi-coherent in every degree. -/
  algebra_isQuasicoherent : ∀ n : ℤ, (𝒜 n).IsQuasicoherent
  /-- The ambient relative projective-spectrum functor as a Zariski sheaf on schemes. -/
  toSheaf : Sheaf Scheme.zariskiTopology (Type u)
  /-- The standard chart functor in each positive degree. -/
  degreeFunctor : ∀ d : { n : ℕ // 1 ≤ n }, Scheme.RelativeProjDegreeFunctor S 𝒜 d.1
  /-- The canonical degreewise identification with geometric quadruples. -/
  degreeAssociated : ∀ d : { n : ℕ // 1 ≤ n }, (degreeFunctor d).IsAssociatedToQuadruples
  /-- Every positive-degree chart functor is representable. -/
  degreeFunctor_isRepresentable :
    ∀ d : { n : ℕ // 1 ≤ n }, (degreeFunctor d).toFunctor.IsRepresentable
  /-- The canonical map from each positive-degree chart to the ambient functor. -/
  degreeToFunctor :
    ∀ d : { n : ℕ // 1 ≤ n }, (degreeFunctor d).toFunctor ⟶ toSheaf.1
  /-- The ambient chart maps respect the actual tensor-power/Veronese transitions.
  This is part of the relative-Proj presentation, not a theorem about arbitrary
  independently glued copies of the degree charts. -/
  degreeToFunctor_transition :
    ∀ (d e : { n : ℕ // 1 ≤ n }) (h : d.1 ∣ e.1),
      (degreeAssociated d).transition (degreeAssociated e) h ≫ degreeToFunctor e =
        degreeToFunctor d
  /-- Each canonical chart map is a relatively representable open immersion of presheaves. -/
  degreeToFunctor_isOpenImmersion :
    ∀ d : { n : ℕ // 1 ≤ n }, IsOpenImmersion.presheaf (degreeToFunctor d)
  /-- The positive-degree chart maps jointly cover the ambient functor in the big Zariski
  topology. -/
  coveredByDegree :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc degreeToFunctor)

namespace RelativeProjFunctor

/-- The contravariant set-valued functor carried by a relative projective-spectrum functor. -/
abbrev toFunctor
    (F : RelativeProjFunctor S 𝒜) : Schemeᵒᵖ ⥤ Type u :=
  F.toSheaf.1

/-- A relative projective-spectrum functor covered by representable open charts is
representable. -/
instance instIsRepresentable
    [F : RelativeProjFunctor S 𝒜] :
    F.toFunctor.IsRepresentable := sorry

end RelativeProjFunctor

end

end AlgebraicGeometry
