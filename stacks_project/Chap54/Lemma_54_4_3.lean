module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.PointBlowup
import StacksCheckRecall

/-!
# Source erratum for tag 0C5H

The pinned source, `additional-sources-1.md` at line 157521, lemma
`lemma-extend-rational-map-blowing-up`, omits global Noetherianity of `X`.
Its proof uses finiteness of the codimension-two complement and then applies
`lemma-dominate-by-blowing-up-in-points`, which assumes a Noetherian scheme.
The source definition of regularity (`properties.tex`, `definition-regular`,
near line 1133) only implies locally Noetherian, not globally Noetherian.

The omitted finiteness condition is necessary for the statement as written: take the
infinite disjoint union of copies of the affine plane over a field, and on
each punctured plane take the rational map `[x:y]` to the same projective
line. Every origin is an indeterminacy point. An extension at an origin would
make either `y/x` or `x/y` regular there, which is impossible. A finite sequence
of single closed-point blowups affects only finitely many original components,
so cannot resolve this map on all components.

The corrected statement below makes this finiteness explicit through
`[CompactSpace X]`; regularity already supplies local Noetherianity. This is the
smallest source correction needed to prevent the non-quasi-compact counterexample
above, while retaining the source's regularity and dimension assumptions. The
pinned original text is left unchanged.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PartialMap

/-- Lemma 54.4.3: For an `S`-rational map from a quasi-compact regular two-dimensional scheme `X`
to a proper `S`-scheme `Y`, a finite sequence of closed-point blowups away from the map's domain
admits an `S`-morphism extending the partial map. -/
@[stacks 0C5H]
theorem exists_pointBlowupSequence_lift_of_compact
  : ∀
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [CompactSpace X] [Scheme.Regular X] [IsProper (Y ↘ S)]
    (f : X.PartialMap Y) [f.IsOver S] (h_dim : topologicalKrullDim X = 2),
    ∃ (Xn : Scheme.{u}) (s : Scheme.PointBlowupSequence X Xn) (g : Xn ⟶ Y),
      s.EveryCenterOver (f.domain : Set X)ᶜ ∧
        (g ≫ (Y ↘ S) = s.toSource ≫ (X ↘ S) ∧
          (s.toSource ⁻¹ᵁ f.domain).ι ≫ g =
            (s.toSource ∣_ f.domain) ≫ f.hom) := sorry

end AlgebraicGeometry.Scheme.PartialMap
