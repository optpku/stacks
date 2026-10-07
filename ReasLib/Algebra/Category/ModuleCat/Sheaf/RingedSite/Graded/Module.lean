module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra

/-!
# Graded module sheaves

This leaf owns right modules over an algebra sheaf graded by a small additive monoid on an arbitrary
ringed site,
together with their category and the forgetful functor to graded module sheaves.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- Definition 24.4.1 (1): a graded module sheaf over `𝒜` is a degreewise family of
`𝒪`-module sheaves with a restriction-compatible right graded `𝒜`-action satisfying associativity
and the unit law. -/
@[stacks 0FQZ]
structure GradedModuleSheaf (𝒜 : GradedAlgebraSheaf 𝒪 ι) where
  /-- The degreewise family of `𝒪`-module sheaves. -/
  obj : ι → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)
  /-- The degreewise right action on local sections. -/
  smul (n m : ι) (U : Cᵒᵖ) :
      (obj n).val.obj U →ₗ[𝒪.obj.obj U]
        (𝒜 m).val.obj U →ₗ[𝒪.obj.obj U] (obj (n + m)).val.obj U
  /-- The action maps commute with restriction. -/
  map_smul {n m : ι} {U V : Cᵒᵖ} (f : U ⟶ V)
      (x : (obj n).val.obj U) (a : (𝒜 m).val.obj U) :
      (((obj (n + m)).val.map f).hom) (smul n m U x a) =
        smul n m V (((obj n).val.map f).hom x) (((𝒜 m).val.map f).hom a)
  /-- The action is associative with the graded multiplication on `𝒜`. -/
  smul_assoc (n m l : ι) (U : Cᵒᵖ)
      (x : (obj n).val.obj U) (a : (𝒜 m).val.obj U) (b : (𝒜 l).val.obj U) :
      HEq (smul (n + m) l U (smul n m U x a) b)
        (smul n (m + l) U x (𝒜.mul U m l a b))
  /-- The degree-zero unit section acts trivially. -/
  smul_one (n : ι) (U : Cᵒᵖ) (x : (obj n).val.obj U) :
      HEq (smul n 0 U x (𝒜.one U)) x

namespace GradedModuleSheaf

/-- Scoped notation for the category of graded right modules over a graded algebra sheaf. -/
scoped[SheafOfModules.RingedSite.GradedModuleSheaf] notation:max "Mod(" 𝒜:arg ")" =>
  _root_.SheafOfModules.RingedSite.GradedModuleSheaf 𝒜

end GradedModuleSheaf

open scoped SheafOfModules.RingedSite.GradedModuleSheaf

/-- A graded module sheaf evaluates to its degreewise module-sheaf family. -/
instance instCoeFun (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    CoeFun (Mod(𝒜))
      (fun _ ↦ ι → SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) where
  coe ℳ := ℳ.obj

namespace GradedModuleSheaf

/-- The underlying graded object of a graded module sheaf. -/
abbrev toGradedObject {𝒜 : GradedAlgebraSheaf 𝒪 ι} (ℳ : Mod(𝒜)) :
    GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) :=
  ℳ.obj

/-- A graded module sheaf coerces to its underlying graded object. -/
instance instCoeOut {𝒜 : GradedAlgebraSheaf 𝒪 ι} :
    CoeOut (Mod(𝒜))
      (GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪))) where
  coe ℳ := ℳ.toGradedObject

/-- The degree-`n` term of the underlying graded object is the degree-`n` module sheaf. -/
@[simp]
theorem toGradedObject_apply {𝒜 : GradedAlgebraSheaf 𝒪 ι} (ℳ : Mod(𝒜)) (n : ι) :
    ℳ.toGradedObject n = ℳ n := sorry

/-- Coercion of a graded module sheaf recovers its degree-`n` component. -/
@[simp]
theorem coe_apply {𝒜 : GradedAlgebraSheaf 𝒪 ι} (ℳ : Mod(𝒜)) (n : ι) :
    ℳ n = ℳ.obj n := sorry

/-- The degree-`n` local sections of a graded module sheaf. -/
abbrev sections {𝒜 : GradedAlgebraSheaf 𝒪 ι} (ℳ : Mod(𝒜)) (U : Cᵒᵖ) (n : ι) :
    Type (max u v) :=
  (ℳ n).val.obj U

/-- Definition 24.4.1 (2): a homomorphism of graded module sheaves is a degreewise family of
`𝒪`-module sheaf morphisms compatible with the graded action. -/
@[stacks 0FQZ, ext]
structure Hom {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ 𝒩 : Mod(𝒜)) where
  /-- The degreewise module-sheaf maps. -/
  hom (n : ι) : ℳ n ⟶ 𝒩 n
  /-- Compatibility with the right action. -/
  comm (n m : ι) (U : Cᵒᵖ) (x : ℳ.sections U n) (a : 𝒜.sections U m) :
      ((hom (n + m)).val.app U).hom (ℳ.smul n m U x a) =
        𝒩.smul n m U (((hom n).val.app U).hom x) a

/-- A graded module sheaf homomorphism evaluates degreewise. -/
instance instCoeFunHom {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ 𝒩 : Mod(𝒜)) : CoeFun (Hom ℳ 𝒩) (fun _ ↦ ∀ n : ι, ℳ n ⟶ 𝒩 n) where
  coe f := f.hom

/-- Associativity of the graded action as an equality after the degree-index transport. -/
theorem smul_assoc_cast {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ : Mod(𝒜)) (n m l : ι) (U : Cᵒᵖ)
    (x : ℳ.sections U n) (a : 𝒜.sections U m) (b : 𝒜.sections U l) :
    cast (congrArg (ℳ.sections U) (add_assoc n m l))
        (ℳ.smul (n + m) l U (ℳ.smul n m U x a) b) =
      ℳ.smul n (m + l) U x (𝒜.mul U m l a b) := sorry

/-- The degree-zero unit action as an equality after the degree-index transport. -/
theorem smul_one_cast {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ : Mod(𝒜)) (n : ι) (U : Cᵒᵖ) (x : ℳ.sections U n) :
    cast (congrArg (ℳ.sections U) (add_zero n))
      (ℳ.smul n 0 U x (𝒜.one U)) = x := sorry

namespace Hom

/-- The identity homomorphism of a graded module sheaf. -/
def id {𝒜 : GradedAlgebraSheaf 𝒪 ι} (ℳ : Mod(𝒜)) : Hom ℳ ℳ where
  hom := fun n ↦ 𝟙 (ℳ n)
  comm := sorry

/-- The composite of graded module sheaf homomorphisms. -/
def comp {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ : Mod(𝒜)} {𝒩 : Mod(𝒜)} {P : Mod(𝒜)}
    (f : Hom ℳ 𝒩) (g : Hom 𝒩 P) : Hom ℳ P where
  hom := fun n ↦ f.hom n ≫ g.hom n
  comm := sorry

/-- The degree-`n` component of the identity is the identity. -/
@[simp]
theorem id_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι} (ℳ : Mod(𝒜)) (n : ι) :
    (id ℳ).hom n = 𝟙 (ℳ n) := sorry

/-- The degree-`n` component of a composite is the composite of degree-`n` components. -/
@[simp]
theorem comp_hom {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ : Mod(𝒜)} {𝒩 : Mod(𝒜)} {P : Mod(𝒜)}
    (f : Hom ℳ 𝒩) (g : Hom 𝒩 P) (n : ι) :
    (comp f g).hom n = f.hom n ≫ g.hom n := sorry

end Hom

/-- Coercion of a graded module sheaf homomorphism recovers its degree-`n` component. -/
@[simp]
theorem hom_coe_apply {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ 𝒩 : Mod(𝒜)} (f : Hom ℳ 𝒩) (n : ι) :
    f n = f.hom n := sorry

/-- Two graded module sheaf homomorphisms are equal when their degreewise components agree. -/
@[ext]
theorem hom_ext {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ 𝒩 : Mod(𝒜)} (f g : Hom ℳ 𝒩)
    (h : ∀ n : ι, f n = g n) : f = g := sorry

/-- The underlying graded-object map determines a graded module sheaf homomorphism. -/
theorem hom_injective {𝒜 : GradedAlgebraSheaf 𝒪 ι} {ℳ 𝒩 : Mod(𝒜)} :
    Function.Injective (fun f : Hom ℳ 𝒩 ↦ f.hom) := sorry

/-- Degreewise identities and compositions give graded module sheaves their category structure. -/
instance instCategory (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    Category (Mod(𝒜)) where
  Hom ℳ 𝒩 := Hom ℳ 𝒩
  id := Hom.id
  comp := Hom.comp
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The category of graded module sheaves, retained as a named API for source-facing uses. -/
@[stacks 0FQZ]
abbrev moduleCategory (𝒜 : GradedAlgebraSheaf 𝒪 ι) := Mod(𝒜)

/-- The named graded-module category is definitionally the bundled graded-module type. -/
@[simp]
theorem moduleCategory_def (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    moduleCategory 𝒜 = Mod(𝒜) := sorry

/-- The forgetful functor from graded module sheaves to their underlying graded module sheaves. -/
def forgetToGraded (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    Mod(𝒜) ⥤ GradedObject ι (SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪)) where
  obj ℳ := ℳ.toGradedObject
  map f := f.hom
  map_id := sorry
  map_comp := sorry

/-- Lemma 24.4.2 (0FR0): evaluation of a graded module sheaf in degree `n`. -/
@[stacks 0FR0 "degree evaluation"]
def eval (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) :
    Mod(𝒜) ⥤ SheafOfModules.{max u v, v, u, max u v} (ringSheaf J 𝒪) :=
  forgetToGraded 𝒜 ⋙ GradedObject.eval n

/-- Evaluating a graded module sheaf in degree `n` returns its `n`th component. -/
@[simp]
theorem eval_obj (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι) (ℳ : Mod(𝒜)) :
    (eval 𝒜 n).obj ℳ = ℳ n := sorry

/-- Evaluation in degree `n` sends a graded-module morphism to its `n`th component. -/
@[simp]
theorem eval_map (𝒜 : GradedAlgebraSheaf 𝒪 ι) (n : ι)
    {ℳ 𝒩 : Mod(𝒜)} (f : ℳ ⟶ 𝒩) :
    (eval 𝒜 n).map f = f.hom n := sorry

/-- Forgetting to the underlying graded object is faithful. -/
instance forgetToGraded_faithful (𝒜 : GradedAlgebraSheaf 𝒪 ι) :
    Functor.Faithful (forgetToGraded 𝒜) where
  map_injective := sorry

/-- The forgetful functor preserves identity maps. -/
@[simp]
theorem forgetToGraded_map_id {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ : Mod(𝒜)) :
    (forgetToGraded 𝒜).map (𝟙 ℳ) = 𝟙 ℳ.toGradedObject := sorry

/-- The forgetful functor preserves composition. -/
@[simp]
theorem forgetToGraded_map_comp {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ 𝒩 P : Mod(𝒜)} (f : ℳ ⟶ 𝒩) (g : 𝒩 ⟶ P) :
    (forgetToGraded 𝒜).map (f ≫ g) =
      (forgetToGraded 𝒜).map f ≫ (forgetToGraded 𝒜).map g := sorry

/-- Forgetting a graded module sheaf recovers its underlying graded object. -/
@[simp]
theorem forgetToGraded_obj {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ : Mod(𝒜)) :
    (forgetToGraded 𝒜).obj ℳ = ℳ.toGradedObject := sorry

/-- Forgetting a graded module sheaf homomorphism recovers its graded-object map. -/
@[simp]
theorem forgetToGraded_map {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ 𝒩 : Mod(𝒜)} (f : ℳ ⟶ 𝒩) :
    (forgetToGraded 𝒜).map f = f.hom := sorry

/-- The forgotten graded object evaluates to the original degree-`n` module sheaf. -/
@[simp]
theorem forgetToGraded_obj_apply {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    (ℳ : Mod(𝒜)) (n : ι) :
    ((forgetToGraded 𝒜).obj ℳ) n = ℳ n := sorry

/-- The forgotten graded-object map evaluates to the original degree-`n` component. -/
@[simp]
theorem forgetToGraded_map_apply {𝒜 : GradedAlgebraSheaf 𝒪 ι}
    {ℳ 𝒩 : Mod(𝒜)} (f : ℳ ⟶ 𝒩) (n : ι) :
    ((forgetToGraded 𝒜).map f) n = f.hom n := sorry

end GradedModuleSheaf

end

end SheafOfModules.RingedSite
