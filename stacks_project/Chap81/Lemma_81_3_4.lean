/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap81.Lemma_81_3_3_EtaleLimit
public import stacks_project.Chap81.Lemma_81_3_4_Coproduct
public import stacks_project.Chap81.Lemma_81_3_4_SeparatedOver

/-!
# Lemma 81.3.4

A separated-over-`B` colimit of algebraic spaces over `B` is a colimit in all of
`Over B` under surjectivity of `∐ X_i ⟶ X`, étale separated base change of that
separated colimit, and an essential-image hypothesis on separated cartesian
spaces-étale systems.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {J : Type v} [Category.{v} J] {S : Scheme.{u}} {B : AlgebraicSpace S}
variable {D : J ⥤ Over B}

/-- A cartesian spaces-étale system lies in the separated essential image of pullback from
`spacesEtaleSite X` when it is isomorphic over `D` to `ofSpacesEtalePullback c U` for some
étale separated `U ⟶ X`. -/
def IsInSeparatedSpacesEtaleEssImage (c : Cocone D)
    (sys : CartesianSpacesEtaleSystem D) : Prop :=
  ∃ (U : spacesEtaleSite c.pt.left),
    Separated U.hom ∧
      ∃ (e : sys.functor ≅ (ofSpacesEtalePullback c U).functor),
        sys.π = e.hom ≫ (ofSpacesEtalePullback c U).π

/-- Separated essential-image membership is an isomorphism over `D` with a pullback of an
étale separated morphism `U ⟶ X`. -/
theorem isInSeparatedSpacesEtaleEssImage_iff (c : Cocone D)
    (sys : CartesianSpacesEtaleSystem D) :
    IsInSeparatedSpacesEtaleEssImage c sys ↔
      ∃ (U : spacesEtaleSite c.pt.left),
        Separated U.hom ∧
          ∃ (e : sys.functor ≅ (ofSpacesEtalePullback c U).functor),
            sys.π = e.hom ≫ (ofSpacesEtalePullback c U).π :=
  sorry

/-- Lemma 81.3.4: Let `S` be a scheme and `B` an algebraic space over `S`. Let `D : J ⥤ Over B`
be a diagram of algebraic spaces over `B`, and let `c` be a cocone for `D` in `Over B`. If each
`X_i` is separated over `B`, the apex `X` is a colimit among algebraic spaces separated over `B`,
the canonical map `∐ X_i ⟶ X` is surjective, étale separated base change preserves that
separated colimit, and every separated cartesian spaces-étale system is a pullback of some
étale separated `U ⟶ X`, then `c` is a colimit in the category of all algebraic spaces over `B`. -/
@[stacks 0GFP]
theorem isColimit_of_separatedOver {J : Type v} [Category.{v} J] [Small.{u} J]
    {S : Scheme.{u}} {B : AlgebraicSpace S} (D : J ⥤ Over B) (c : Cocone D)
    (h_sep : ∀ i, Separated (D.obj i).hom) (h_pt : Separated c.pt.hom)
    (h_colim : IsColimitAmongSeparated c)
    (h_surj : Surjective (coproductToColimit c))
    (h_etale_colim :
      ∀ {U : AlgebraicSpace S} (f : U ⟶ c.pt.left) [Etale f] [Separated f],
        IsColimitAmongSeparated (baseChangeCocone c f))
    (h_ess : ∀ sys : CartesianSpacesEtaleSystem D,
      (∀ i, Separated (sys.π.app i)) → IsInSeparatedSpacesEtaleEssImage c sys) :
    Nonempty (IsColimit c) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
