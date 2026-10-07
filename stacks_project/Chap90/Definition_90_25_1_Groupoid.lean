module

public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap90.Definition_90_21_1_Groupoid

/-!
# Groupoids in functors from groupoid-valued functors

A functor `C ⥤ Grpd` determines a groupoid in functors by taking objects, packaged
arrows, and the source, target, composition, identity, and inverse maps of the fibres.
-/

@[expose] public section

open CategoryTheory Limits TypeCat

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- An arrow of a groupoid, packaged with its source and target. -/
structure PackedArrow (G : Grpd.{w, w}) where
  /-- The source object. -/
  src : G
  /-- The target object. -/
  tgt : G
  /-- The underlying morphism. -/
  hom : src ⟶ tgt

namespace PackedArrow

/-- The identity arrow on an object of a groupoid. -/
def id {G : Grpd.{w, w}} (x : G) : PackedArrow G where
  src := x
  tgt := x
  hom := 𝟙 x

/-- The source of an identity arrow is the given object. -/
theorem id_src {G : Grpd.{w, w}} (x : G) : (id x).src = x := sorry

/-- The inverse of a packaged groupoid arrow. -/
def inverse {G : Grpd.{w, w}} (a : PackedArrow G) : PackedArrow G where
  src := a.tgt
  tgt := a.src
  hom := Groupoid.inv a.hom

/-- The source of an inverse arrow is the original target. -/
theorem inverse_src {G : Grpd.{w, w}} (a : PackedArrow G) : (inverse a).src = a.tgt := sorry

/-- The image of a packaged arrow under a functor of groupoids. -/
def map {G H : Grpd.{w, w}} (F : G ⥤ H) (a : PackedArrow G) : PackedArrow H where
  src := F.obj a.src
  tgt := F.obj a.tgt
  hom := F.map a.hom

/-- Mapping a packaged arrow preserves sources. -/
theorem map_src {G H : Grpd.{w, w}} (F : G ⥤ H) (a : PackedArrow G) :
    (map F a).src = F.obj a.src := sorry

/-- Composite of a later packaged arrow with an earlier packaged arrow. -/
def comp {G : Grpd.{w, w}} (later earlier : PackedArrow G) (h : later.src = earlier.tgt) :
    PackedArrow G where
  src := earlier.src
  tgt := later.tgt
  hom := earlier.hom ≫ eqToHom h.symm ≫ later.hom

/-- The source of a packaged composite is the source of the earlier arrow. -/
theorem comp_src {G : Grpd.{w, w}} (later earlier : PackedArrow G)
    (h : later.src = earlier.tgt) : (comp later earlier h).src = earlier.src := sorry

end PackedArrow

/-- The functor of packaged arrows of a groupoid-valued functor. -/
def packedArrowFunctor (F : C ⥤ Grpd.{w, w}) : C ⥤ Type w where
  obj T := PackedArrow (F.obj T)
  map f := ofHom fun a ↦ PackedArrow.map (F.map f) a
  map_id := sorry
  map_comp := sorry

/-- Evaluating the packed-arrow functor recovers the packaged arrows of the fibre. -/
theorem packedArrowFunctor_obj (F : C ⥤ Grpd.{w, w}) (T : C) :
    (packedArrowFunctor F).obj T = PackedArrow (F.obj T) := sorry

/-- The source natural transformation of the packed-arrow functor. -/
def packedArrowSource (F : C ⥤ Grpd.{w, w}) :
    packedArrowFunctor F ⟶ F ⋙ Grpd.objects where
  app T := ofHom fun a ↦ a.src
  naturality := sorry

/-- The source component of a packaged arrow is its source object. -/
theorem packedArrowSource_app (F : C ⥤ Grpd.{w, w}) (T : C)
    (a : PackedArrow (F.obj T)) : (packedArrowSource F).app T a = a.src := sorry

/-- The target natural transformation of the packed-arrow functor. -/
def packedArrowTarget (F : C ⥤ Grpd.{w, w}) :
    packedArrowFunctor F ⟶ F ⋙ Grpd.objects where
  app T := ofHom fun a ↦ a.tgt
  naturality := sorry

/-- The target component of a packaged arrow is its target object. -/
theorem packedArrowTarget_app (F : C ⥤ Grpd.{w, w}) (T : C)
    (a : PackedArrow (F.obj T)) : (packedArrowTarget F).app T a = a.tgt := sorry

/-- Pointwise composition of packaged arrows in a pullback of source against target. -/
def packedArrowCompositionApp (F : C ⥤ Grpd.{w, w}) (T : C)
    (p : (pullback (packedArrowSource F) (packedArrowTarget F)).obj T) :
    PackedArrow (F.obj T) :=
  let s := packedArrowSource F
  let t := packedArrowTarget F
  let later := (pullback.fst s t).app T p
  let earlier := (pullback.snd s t).app T p
  PackedArrow.comp later earlier
    (_root_.congr_arg
      (fun f : (pullback s t).obj T ⟶ (F ⋙ Grpd.objects).obj T ↦ f p)
      (NatTrans.congr_app
        (pullback.condition : pullback.fst s t ≫ s = pullback.snd s t ≫ t) T))

/-- The composition natural transformation of the packed-arrow functor. -/
def packedArrowComposition (F : C ⥤ Grpd.{w, w}) :
    pullback (packedArrowSource F) (packedArrowTarget F) ⟶ packedArrowFunctor F where
  app T := ofHom fun p ↦ packedArrowCompositionApp F T p
  naturality := sorry

/-- Composition in a fibre is the packaged composite of the later and earlier arrows. -/
theorem packedArrowComposition_app (F : C ⥤ Grpd.{w, w}) (T : C)
    (p : (pullback (packedArrowSource F) (packedArrowTarget F)).obj T) :
    (packedArrowComposition F).app T p = packedArrowCompositionApp F T p := sorry

/-- The identity-arrow natural transformation of a groupoid-valued functor. -/
def packedArrowIdentity (F : C ⥤ Grpd.{w, w}) :
    F ⋙ Grpd.objects ⟶ packedArrowFunctor F where
  app T := ofHom fun x ↦ PackedArrow.id x
  naturality := sorry

/-- The identity transformation sends each object to its identity arrow. -/
theorem packedArrowIdentity_app (F : C ⥤ Grpd.{w, w}) (T : C) (x : F.obj T) :
    (packedArrowIdentity F).app T x = PackedArrow.id x := sorry

/-- The inverse-arrow natural transformation of a groupoid-valued functor. -/
def packedArrowInverse (F : C ⥤ Grpd.{w, w}) :
    packedArrowFunctor F ⟶ packedArrowFunctor F where
  app T := ofHom fun a ↦ PackedArrow.inverse a
  naturality := sorry

/-- The inverse transformation sends each packaged arrow to its inverse. -/
theorem packedArrowInverse_app (F : C ⥤ Grpd.{w, w}) (T : C)
    (a : PackedArrow (F.obj T)) :
    (packedArrowInverse F).app T a = PackedArrow.inverse a := sorry

namespace GroupoidInFunctors

/-- Reconstruct a groupoid in functors from a functor to groupoids. -/
def ofFunctor (F : C ⥤ Grpd.{w, w}) : GroupoidInFunctors.{u, v, w} C where
  U := F ⋙ Grpd.objects
  R := packedArrowFunctor F
  s := packedArrowSource F
  t := packedArrowTarget F
  c := packedArrowComposition F
  e := packedArrowIdentity F
  i := packedArrowInverse F
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object functor of `ofFunctor F` is `F ⋙ Grpd.objects`. -/
theorem ofFunctor_U (F : C ⥤ Grpd.{w, w}) :
    (ofFunctor F).U = F ⋙ Grpd.objects := sorry

/-- The arrow functor of `ofFunctor F` is the packed-arrow functor of `F`. -/
theorem ofFunctor_R (F : C ⥤ Grpd.{w, w}) :
    (ofFunctor F).R = packedArrowFunctor F := sorry

/-- Passing from a functor `C ⥤ Grpd` to a groupoid in functors and back preserves objects. -/
theorem toFunctor_ofFunctor_objects (F : C ⥤ Grpd.{w, w}) :
    (ofFunctor F).toFunctor ⋙ Grpd.objects = F ⋙ Grpd.objects := sorry

end GroupoidInFunctors

end CategoryTheory

