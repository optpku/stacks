module

public import stacks_project.Chap70.Lemma_70_14_7_Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y U V : AlgebraicSpace S}
variable (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
variable (ιV : V ⟶ Y) [IsOpenImmersion ιV] [QuasiCompact ιV]
variable (ιU : U ⟶ X) [IsOpenImmersion ιU] (f' : U ⟶ V)
variable (h_cart : IsPullback ιU f' f ιV)
variable (F : X.Modules) [F.IsQuasicoherent] (W : smallEtaleSite Y)

/-
Lemma 70.14.7: let `S` be a scheme and `f : X ⟶ Y` a quasi-compact and quasi-separated
morphism of algebraic spaces over `S`. Let `T ⊂ |Y|` be a closed subset whose complement
corresponds to an open subspace `V ⊂ Y` with quasi-compact morphism `V ⟶ Y`. Let `F` be a
quasi-coherent `𝒪_X`-module, and let `F' ⊂ F` be the subsheaf of sections supported on
`|f|⁻¹ T`. Then `f_* F' ⊂ f_* F` is the subsheaf of sections supported on `T`. The complement
of `|f|⁻¹ T` is the support of the open subspace `U = f⁻¹ V ⊂ X`, presented by a cartesian
square over `V ⟶ Y`.
-/
@[stacks 085B]
#check (range_pushforward_sectionsWithSupportInι_app_eq f ιV ιU f' h_cart F W :
  Set.range (((pushforward f).map (sectionsWithSupportInι ιU F)).val.app (op W)) =
    Set.range ((sectionsWithSupportInι ιV ((pushforward f).obj F)).val.app (op W)))

end AlgebraicGeometry.AlgebraicSpace.Modules
