module

public import ReasLib.Topology.Opens.Instances
public import ReasLib.Topology.Sheaf.ExtensionByInitial
public import ReasLib.Topology.Sheaf.Notation
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Lower-shriek constant sheaves

For an open subspace `U` of `X`, this module owns the functor sending `S` to the extension
`j![U, S]` and its universal description: morphisms from `j![U, S]` to a sheaf `F` are functions
from `S` to the sections `F(U)`.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open TopCat.Opens.Subspace

noncomputable section

universe u

namespace TopCat.Sheaf.ExtensionByInitial.Constant

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- The functor `S ↦ j![U, S]` from types to sheaves on `X`. -/
@[stacks 0CAH "lower-shriek constant functor"]
noncomputable def functor (U : Opens X) :
    Type u ⥤ TopCat.Sheaf (Type u) X :=
  CategoryTheory.constantSheaf
      (Opens.grothendieckTopology (space U)) (Type u) ⋙
    TopCat.Sheaf.ExtensionByInitial.functor U

/-- The lower-shriek extension `j![U, S]` of the constant sheaf on `S`. -/
noncomputable abbrev obj (U : Opens X) (S : Type u) :
    TopCat.Sheaf (Type u) X :=
  (functor U).obj S

/-- The comparison between sections of the categorical pullback to `U` over its top open and
sections of the original sheaf over `U`. -/
noncomputable def pullbackTopSectionIso
    (U : Opens X) (F : TopCat.Sheaf (Type u) X) :
    ((TopCat.Sheaf.pullback (Type u) (inclusion U)).obj F).presheaf.obj
        (op (⊤ : Opens (space U))) ≅
      F.presheaf.obj (op U) :=
  (((TopCat.Sheaf.forget (Type u) (space U)).mapIso
      ((U.isOpenEmbedding.sheafPullbackIso (Type u)).app F)).app
        (op (⊤ : Opens (space U)))) ≪≫
    F.presheaf.mapIso
      (eqToIso (congrArg op (Opens.isOpenEmbedding_obj_top U)))

/-- Morphisms `j![U, S] ⟶ F` are naturally equivalent to `S`-indexed sections of
`F` over `U`. -/
noncomputable def homEquivSection
    (U : Opens X) (S : Type u) (F : TopCat.Sheaf (Type u) X) :
    (obj U S ⟶ F) ≃ (S → F.presheaf.obj (op U)) :=
  ((((TopCat.Sheaf.ExtensionByInitial.Properties.adjunction
      (C := Type u) U).homEquiv _ _).trans
    ((CategoryTheory.constantSheafAdj
      (Opens.grothendieckTopology (space U)) (Type u)
      (Preorder.isTerminalTop (Opens (space U)))).homEquiv _ _)).trans
    TypeCat.homEquiv).trans
    (Equiv.piCongrRight (fun _ ↦ (pullbackTopSectionIso U F).toEquiv))

/-- `homEquivSection` turns precomposition by a map of indexing types into precomposition of
the corresponding families of sections. -/
theorem homEquivSection_naturality_left
    {U : Opens X} {S T : Type u} (f : S ⟶ T)
    (F : TopCat.Sheaf (Type u) X) (alpha : obj U T ⟶ F) :
    homEquivSection U S F ((functor U).map f ≫ alpha) =
      fun s ↦ homEquivSection U T F alpha (f s) := sorry

/-- The inverse of `homEquivSection` commutes with precomposition by a map of indexing types. -/
theorem homEquivSection_naturality_left_symm
    {U : Opens X} {S T : Type u} (f : S ⟶ T)
    (F : TopCat.Sheaf (Type u) X) (g : T → F.presheaf.obj (op U)) :
    (homEquivSection U S F).symm (fun s ↦ g (f s)) =
      (functor U).map f ≫ (homEquivSection U T F).symm g := sorry

/-- `homEquivSection` turns postcomposition of sheaf morphisms into pointwise application on
sections. -/
theorem homEquivSection_naturality_right
    {U : Opens X} {S : Type u}
    {F G : TopCat.Sheaf (Type u) X} (alpha : obj U S ⟶ F) (phi : F ⟶ G) :
    homEquivSection U S G (alpha ≫ phi) =
      fun s ↦ phi.hom.app (op U) (homEquivSection U S F alpha s) := sorry

/-- The inverse of `homEquivSection` commutes with postcomposition of sheaf morphisms. -/
theorem homEquivSection_naturality_right_symm
    {U : Opens X} {S : Type u} {F G : TopCat.Sheaf (Type u) X}
    (g : S → (F.presheaf.obj (op U))) (phi : F ⟶ G) :
    (homEquivSection U S G).symm
        (fun s ↦ phi.hom.app (op U) (g s)) =
      (homEquivSection U S F).symm g ≫ phi := sorry

end TopCat.Sheaf.ExtensionByInitial.Constant

namespace TopCat

/-- Notation for the lower-shriek constant sheaf `j![U, S]`. -/
scoped notation:max "j![" U ", " S "]" =>
  TopCat.Sheaf.ExtensionByInitial.Constant.obj U S

end TopCat

end

end
