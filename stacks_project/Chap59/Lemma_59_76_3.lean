/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Definition_59_76_1
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Derived
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable (f : X ⟶ Y)
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Z : Scheme.{u}) (U : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ (Z W : Scheme.{u}) (g : Z ⟶ W) (P : W.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [hAdd : @CategoryTheory.Functor.Additive
    (Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ))
    (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) _ _
    Abelian.toPreadditive Abelian.toPreadditive
    (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
variable [PreservesFiniteLimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]
variable [PreservesFiniteColimits (Sheaf.smallEtaleInverseImage f (ModuleCat.{v} Λ))]

/- Lemma 59.76.3: if `Λ` is Noetherian, `f : X ⟶ Y` is a morphism of schemes, and
`K` is an object of `D_c(Yₑₜ, Λ)`, then the derived inverse image
`Lf^* K` lies in `D_c(Xₑₜ, Λ)`. -/
@[stacks 095Y] #check
  (AlgebraicGeometry.Scheme.smallEtaleInverseImageDerived_mem_constructibleCategory f :
    ∀ K : EtaleConstructibleCategory Y Λ
      (Sheaf.IsConstructibleEtaleModule (X := Y)
        (fun {_} g ↦ (Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
        (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)),
      DerivedCategory.cohomologyIn
        (Sheaf.IsConstructibleEtaleModule (X := X)
          (fun {_} g ↦ (Sheaf.smallEtaleInverseImage g (ModuleCat.{v} Λ)).obj)
          (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
        ((smallEtaleInverseImageDerived f).obj K.obj))

end AlgebraicGeometry.Scheme
