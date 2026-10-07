module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Definition_87_9_1_Affine

/-!
# Lemma 87.36.1

A directed colimit of affine formal algebraic spaces along closed immersions
inducing isomorphisms on reductions is again an affine formal algebraic space.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- A morphism of fppf sheaves is a relative thickening when it is relatively
representable and every represented pullback is a thickening of schemes. -/
def isRelativeThickening {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) : Prop :=
  (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor f

/-- Relative thickening unpacks as relative representability together with
thickenings of represented pullbacks on source schemes, i.e. closed immersions
inducing isomorphisms on scheme reductions. -/
theorem isRelativeThickening_iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y) :
    isRelativeThickening f ↔
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
        ∀ {U V : 𝒮.bigSite S}
          (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y)
          (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
          IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) f ξ →
            IsThickening ((𝒮.bigToScheme S).map snd) :=
  sorry

/-- Lemma 87.36.1: Let `S` be a scheme. Suppose given a directed set `Λ` and a
system of affine formal algebraic spaces `(X_λ, f_λμ)` over `Λ` where each
`f_λμ : X_λ ⟶ X_μ` is a closed immersion inducing an isomorphism
`X_λ,red ⟶ X_μ,red`. Then `X = colim_λ X_λ` is an affine formal algebraic
space over `S`. The transition hypothesis is the section's representable
thickening condition. -/
@[stacks 0GVM]
theorem of_directedColimit {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {Λ : Type (max u v)} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (F : Λ ⥤ Sheaf (𝒮.bigTopology S) (Type (max u v)))
    (h_affine : ∀ i, IsAffineFormalAlgebraicSpace (F.obj i))
    (h_thickening : ∀ {i j : Λ} (f : i ⟶ j), isRelativeThickening (F.map f))
    (c : Cocone F) (hc : IsColimit c) :
    IsAffineFormalAlgebraicSpace c.pt :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
