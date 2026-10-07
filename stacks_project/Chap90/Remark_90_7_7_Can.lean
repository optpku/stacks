module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Lemma_90_7_4_Along
public import stacks_project.Chap90.Remark_90_7_7_Nilpotency

/-!
# Restriction of the completion to `C_Λ` and the evaluation functor `can`

Objects of `FormalObject.Restrict p` are formal objects of `p` whose complete local
base is the image of an Artinian algebra. The functor `can` evaluates a formal object
at the nilpotency stage and transports along `truncationNilpotencyIso`. A quasi-inverse
`toRestrict` realises `F` as a full subcategory of formal objects via `embed`.
-/

@[expose] public section

open CategoryTheory IsLocalRing Opposite ArtinianLocalAlgCat
open scoped BasedFunctor

noncomputable section

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

/-- The restriction of `hat F` to `C_Λ`: a formal object of `p` together with an Artinian
base identified with its complete local view. -/
structure Restrict (p : F ⥤ ArtinianLocalAlgCat Λ k) where
  /-- Underlying formal object of `p`. -/
  formal : FormalObject p
  /-- Artinian base of the restricted object. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The formal object lies over the complete-local view of `base`. -/
  over : formal.base = toComplete base

namespace Restrict

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Package a completion fibre over `toComplete A` as an object of the restriction. -/
noncomputable def of [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) : Restrict p where
  formal := ξ.1
  base := A
  over := ξ.2

/-- The formal object of a packaged fibre is the fibre representative. -/
theorem of_formal [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    (of A ξ).formal = ξ.1 := sorry

/-- The Artinian base of a packaged fibre is the supplied algebra. -/
theorem of_base [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    (of A ξ).base = A := sorry

/-- An object of the restriction is a formal object over `toComplete` of its Artinian base. -/
theorem spec (ξ : Restrict p) :
    ξ.formal.base = toComplete ξ.base := sorry

/-- A morphism of restricted formal objects is a morphism of formal objects together with an
Artinian base map compatible with inclusion into complete local algebras. -/
structure Hom (ξ η : Restrict p) where
  /-- Underlying morphism of formal objects. -/
  formal : ξ.formal ⟶ η.formal
  /-- Underlying morphism of Artinian bases. -/
  base : ξ.base ⟶ η.base
  /-- The complete-local view of `base` recovers the formal base map. -/
  over : inclusion.map base =
    eqToHom ξ.over.symm ≫ formal.base ≫ eqToHom η.over

/-- Identity morphism of a restricted formal object. -/
def Hom.id (ξ : Restrict p) : Hom ξ ξ where
  formal := 𝟙 ξ.formal
  base := 𝟙 ξ.base
  over := sorry

/-- Composition of morphisms of restricted formal objects. -/
def Hom.comp {ξ η ζ : Restrict p} (a : Hom ξ η) (b : Hom η ζ) : Hom ξ ζ where
  formal := a.formal ≫ b.formal
  base := a.base ≫ b.base
  over := sorry

/-- A restricted morphism is compatible with inclusion of Artinian bases. -/
theorem Hom.spec {ξ η : Restrict p} (a : Hom ξ η) :
    inclusion.map a.base =
      eqToHom ξ.over.symm ≫ a.formal.base ≫ eqToHom η.over := sorry

/-- Category of formal objects of `p` restricted to `C_Λ`. -/
instance category : Category.{max u v} (Restrict p) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The projection `hat F |_{C_Λ} ⥤ C_Λ` sending a restricted formal object to its Artinian base. -/
def projection (p : F ⥤ ArtinianLocalAlgCat Λ k) : Restrict p ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map a := a.base
  map_id := sorry
  map_comp := sorry

/-- The projection sends a restricted formal object to its stored Artinian base. -/
theorem projection_obj (ξ : Restrict p) : (projection p).obj ξ = ξ.base := sorry

/-- Inclusion of the restriction into the category of all formal objects of `p`. -/
def ι (p : F ⥤ ArtinianLocalAlgCat Λ k) : Restrict p ⥤ FormalObject p where
  obj ξ := ξ.formal
  map a := a.formal
  map_id := sorry
  map_comp := sorry

/-- The inclusion sends a restricted object to its stored formal object. -/
theorem ι_obj (ξ : Restrict p) : (ι p).obj ξ = ξ.formal := sorry

/-- The inclusion of the restriction into formal objects is full. -/
instance ι.full : (ι p).Full := sorry

/-- The inclusion of the restriction into formal objects is faithful. -/
instance ι.faithful : (ι p).Faithful := sorry

/-- The restricted projection is cofibered in groupoids. -/
instance projection_op_isFiberedInGroupoids [Functor.IsFibered.InGroupoids p.op] :
    Functor.IsFibered.InGroupoids (projection p).op := sorry

end Restrict

variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.IsFibered.InGroupoids p.op]

/-- Stage `n` of a restricted formal object lies over the corresponding truncation of its
Artinian base. -/
def stageOver (ξ : Restrict p) (n : ℕ) :
    p.obj (ξ.formal.system.family n) = (toComplete ξ.base).truncation n :=
  (ξ.formal.over_obj n).trans (congrArg (fun R ↦ R.truncation n) ξ.over)

/-- Evaluation of a restricted formal object at its nilpotency stage, transported to the
Artinian base along `truncationNilpotencyIso`. -/
noncomputable def canObj (ξ : Restrict p) : F :=
  Along.pushforwardObj (stageOver ξ (nilpotencyIndex ξ.base))
    (truncationNilpotencyIso ξ.base).hom

/-- The cofibered pushforward from the nilpotency stage to `canObj`. -/
noncomputable def canPush (ξ : Restrict p) :
    ξ.formal.system.family (nilpotencyIndex ξ.base) ⟶ canObj ξ :=
  Along.pushforwardMap (stageOver ξ (nilpotencyIndex ξ.base))
    (truncationNilpotencyIso ξ.base).hom

/-- Induced map from the source nilpotency stage to the target evaluation. -/
noncomputable def canAppAux {ξ η : Restrict p} (a : ξ ⟶ η) :
    ξ.formal.system.family (nilpotencyIndex ξ.base) ⟶ canObj η :=
  let m := nilpotencyIndex ξ.base
  let m' := nilpotencyIndex η.base
  if h : m' ≤ m then
    a.formal.app m ≫ η.formal.system.transitionMap h ≫ canPush η
  else
    let steps := ξ.formal.system.transitionMap (le_of_not_ge h)
    let φ := Quiver.Hom.op steps
    let f := p.op.map φ
    let φ' := Quiver.Hom.op (a.formal.app m' ≫ canPush η)
    Along.cartesianUnop (p := p) f φ φ' inferInstance sorry

/-- The evaluation functor `can : hat F |_{C_Λ} ⥤ F`. -/
noncomputable def can (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] : Restrict p ⥤ F where
  obj ξ := canObj ξ
  map {ξ η} a :=
    let m := nilpotencyIndex ξ.base
    let f := Quiver.Hom.op (truncationNilpotencyIso ξ.base).hom
    let φ := Functor.IsPreFibered.pullbackMap (p := p.op)
      (a := Opposite.op (ξ.formal.system.family m))
      (ha := congrArg Opposite.op (stageOver ξ m)) f
    let g := Quiver.Hom.op a.base
    Along.stronglyCartesianUnop (p := p) f φ g (g ≫ f) rfl (Quiver.Hom.op (canAppAux a))
      inferInstance sorry
  map_id := sorry
  map_comp := sorry

/-- `can` evaluates a restricted formal object at its nilpotency stage. -/
theorem can_obj (ξ : Restrict p) : (can p).obj ξ = canObj ξ := sorry

/-- The evaluation functor lies strictly over `C_Λ`. -/
noncomputable def basedCan (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] :
    BasedCategory.ofFunctor (Restrict.projection p) ⥤ᵇ BasedCategory.ofFunctor p where
  toFunctor := can p
  w := sorry

/-- The based evaluation functor lies over the identity of `C_Λ`. -/
theorem basedCan_w (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] :
    (basedCan p).toFunctor ⋙ p = Restrict.projection p := sorry

/-- Evaluation is an equivalence of categories cofibered in groupoids over `C_Λ`. -/
instance basedCan_isEquivalence :
    BasedFunctor.IsEquivalence (basedCan p) := sorry

/-- Package a fibre morphism over `toComplete A` as a restricted morphism over `𝟙 A`. -/
noncomputable def Restrict.ofHom {A : ArtinianLocalAlgCat Λ k}
    {ξ η : Functor.Fiber (Functor.completion p) (toComplete A)}
    (a : ξ ⟶ η) : Restrict.of A ξ ⟶ Restrict.of A η where
  formal := a.1
  base := 𝟙 A
  over := sorry

/-- Fibrewise evaluation of `can` over an Artinian algebra `A`. -/
noncomputable def canFiber (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] (A : ArtinianLocalAlgCat Λ k) :
    Functor.Fiber (Functor.completion p) (toComplete A) ⥤ Functor.Fiber p A where
  obj ξ := ⟨(can p).obj (Restrict.of A ξ), sorry⟩
  map a := ⟨(can p).map (Restrict.ofHom a), sorry⟩
  map_id := sorry
  map_comp := sorry

/-- Fibrewise evaluation sends a completion fibre to the evaluation of the packaged object. -/
theorem canFiber_obj (A : ArtinianLocalAlgCat Λ k)
    (ξ : Functor.Fiber (Functor.completion p) (toComplete A)) :
    Functor.Fiber.fiberInclusion.obj ((canFiber p A).obj ξ) =
      (can p).obj (Restrict.of A ξ) := sorry

/-- Fibrewise evaluation is an equivalence, by Lemma 90.7.4 and the zero filtration. -/
instance canFiber_isEquivalence (A : ArtinianLocalAlgCat Λ k) :
    (canFiber p A).IsEquivalence := sorry

/-- Truncation of an Artinian base map on maximal-adic quotients. -/
noncomputable def truncationMapOf {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (n : ℕ) :
    (toComplete A).truncation n ⟶ (toComplete B).truncation n where
  hom :=
    Ideal.quotientMapₐ (maximalIdeal B.carrier ^ (n + 1)) f.hom
      (sorry : maximalIdeal A.carrier ^ (n + 1) ≤
        (maximalIdeal B.carrier ^ (n + 1)).comap f.hom)
  isLocalHom := sorry
  residue_compat := sorry

/-- Successor map of the constant inverse system obtained by pushing an object of `F`
along truncations of its base. -/
noncomputable def embedStep (x : F) (n : ℕ) :
    Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) (n + 1)) ⟶
      Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n) :=
  let A := p.obj x
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A (n + 1)))
  let φ' := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A n))
  let g :=
    eqToHom (Functor.IsPreFibered.pullbackObj_proj (p := p.op) (a := Opposite.op x)
        (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation A n))) ≫
      Quiver.Hom.op ((toComplete A).truncationMap n)
  let f := Quiver.Hom.op (toTruncation A (n + 1))
  Along.stronglyCartesianUnop (p := p) f φ g (g ≫ f) rfl φ' inferInstance sorry

/-- Stage map of pushed truncations induced by a morphism of `F`. -/
noncomputable def toRestrictApp {x y : F} (f : x ⟶ y) (n : ℕ) :
    Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n) ⟶
      Along.pushforwardObj (rfl : p.obj y = p.obj y) (toTruncation (p.obj y) n) :=
  let φ := Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op x)
    (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation (p.obj x) n))
  let φ' :=
    Functor.IsPreFibered.pullbackMap (p := p.op) (a := Opposite.op y)
      (ha := congrArg Opposite.op rfl) (Quiver.Hom.op (toTruncation (p.obj y) n)) ≫
      Quiver.Hom.op f
  let fst := Quiver.Hom.op (toTruncation (p.obj x) n)
  let g := Quiver.Hom.op (truncationMapOf (p.map f) n)
  Along.stronglyCartesianUnop (p := p) fst φ g (g ≫ fst) rfl φ' inferInstance sorry

/-- The formal object of truncations of an object of `F`. -/
noncomputable def toRestrictFormal (x : F) : FormalObject p :=
  FormalObject.of (toComplete (p.obj x))
    (fun n ↦ Along.pushforwardObj (rfl : p.obj x = p.obj x) (toTruncation (p.obj x) n))
    (fun n ↦ embedStep x n) sorry sorry

/-- Explicit quasi-inverse of `can`, sending an object of `F` to the restricted formal
object of its truncations. -/
noncomputable def toRestrict (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] : F ⥤ Restrict p where
  obj x :=
    { formal := toRestrictFormal x
      base := p.obj x
      over := rfl }
  map {x y} f :=
    { formal :=
        { base := inclusion.map (p.map f)
          app := fun n ↦ toRestrictApp f n
          baseTrunc := fun n ↦ truncationMapOf (p.map f) n
          over := sorry
          baseTrunc_spec := sorry
          naturality := sorry }
      base := p.map f
      over := sorry }
  map_id := sorry
  map_comp := sorry

/-- Inclusion of `F` into formal objects of `p` as the composite of the quasi-inverse
with the restriction inclusion. -/
noncomputable def embed (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op] : F ⥤ FormalObject p :=
  toRestrict p ⋙ Restrict.ι p

/-- The complete local base of an embedded object is the complete-local view of `p.obj x`. -/
theorem embed_base (x : F) : ((embed p).obj x).base = toComplete (p.obj x) := sorry

/-- The embedding of `F` into formal objects is full. -/
instance embed.full : (embed p).Full := sorry

/-- The embedding of `F` into formal objects is faithful. -/
instance embed.faithful : (embed p).Faithful := sorry

end FormalObject

end
