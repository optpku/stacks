module

public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.Construction.DescentEffectivity
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Basic

/-!
# The comparison into cover descent objects

The comparison maps an original fibre object to its descent datum on the maximal
cover. Restriction comparisons use the original pseudofunctor's actual
composition maps in both directions.
-/

@[expose] public section

open CategoryTheory Opposite GrothendieckTopology

noncomputable section

universe u v uF vF

namespace CategoryTheory.Functor.StackificationConstruction.DescentCompletion

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF})

/-- The comparison from the maximal-cover datum of a restriction to the
restriction of the maximal-cover datum uses the original composition inverse. -/
def unitReindexRaw {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) :
    RawHom J F (ofObject J F ((F.map f.op.toLoc).toFunctor.obj x))
      (pullbackObject J F f (ofObject J F x)) where
  cover := ⊤
  left := le_rfl
  right := le_rfl
  arrow :=
    { hom I := (F.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc rfl).inv.toNatTrans.app x
      comm := by sorry }

/-- The reverse comparison uses the original composition map. -/
def unitReindexInverseRaw {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) :
    RawHom J F (pullbackObject J F f (ofObject J F x))
      (ofObject J F ((F.map f.op.toLoc).toFunctor.obj x)) where
  cover := ⊤
  left := le_rfl
  right := le_rfl
  arrow :=
    { hom I := (F.mapComp' f.op.toLoc I.f.op.toLoc (I.f ≫ f).op.toLoc rfl).hom.toNatTrans.app x
      comm := by sorry }

/-- Both directions of the unit's restriction comparison are explicit classes. -/
def unitReindexIso {U V : C} (f : V ⟶ U) (x : F.obj (.mk (op U))) :
    ofObject J F ((F.map f.op.toLoc).toFunctor.obj x) ≅
      pullbackObject J F f (ofObject J F x) where
  hom := _root_.Quotient.mk'' (unitReindexRaw J F f x)
  inv := _root_.Quotient.mk'' (unitReindexInverseRaw J F f x)
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The restriction comparisons are natural in the original fibre object. -/
def unitReindex {U V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor ⋙ unitFunctor J F V ≅
      unitFunctor J F U ⋙ pullbackFunctor J F f :=
  NatIso.ofComponents (unitReindexIso J F f) (by sorry)

/-- The original pseudofunctor maps to its descent completion through the
actual maximal-cover functors and the actual restriction comparisons. -/
def unitIndexedFunctor : Pseudofunctor.LocallyDiscreteOpToCat.IndexedFunctor
    (𝟭 C) F (presheaf J F).toPseudofunctor' where
  app U := unitFunctor J F U
  naturality f := unitReindex J F f
  naturality_id := sorry
  naturality_comp := sorry

end CategoryTheory.Functor.StackificationConstruction.DescentCompletion
