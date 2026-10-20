module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import ReasLib.RingTheory.Algebra.TensorProduct.Map

@[expose] public section

open CategoryTheory Limits
open Algebra.TensorProduct
open scoped TensorProduct

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {J : Type v} [SmallCategory J] [IsFiltered J]
variable (F : J ⥤ CommAlgCat.{u} A) [HasColimit F]

/-- Helper for Lemma 10.127.7: the backend `Under`-valued tensor diagram obtained by transporting
the given `A`-algebra diagram through `CommAlgCat ≃ Under` and tensoring with `S`. -/
abbrev tensor_base_change_backend_under_diagram
    (S : Type u) [CommRing S] [Algebra A S] :
    J ⥤ Under (CommRingCat.of S) :=
  F ⋙ (commAlgCatEquivUnder (CommRingCat.of A)).functor ⋙
    CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)

/-- Helper for Lemma 10.127.7: the tensor transition maps form a functor on the literal tensor
stages. -/
lemma tensor_base_change_diagram_map_id
    (S : Type u) [CommRing S] [Algebra A S] (j : J) :
    CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (𝟙 j)).hom).toRingHom =
      𝟙 (CommRingCat.of (S ⊗[A] ↑(F.obj j))) := by
  -- Proof comment: tensoring by the identity on the right gives the identity endomorphism.
  ext
  · simp
  · simp

/-- Helper for Lemma 10.127.7: tensor transition maps compose as expected along the filtered
diagram. -/
lemma tensor_base_change_diagram_map_comp
    (S : Type u) [CommRing S] [Algebra A S]
    {j j' j'' : J} (f : j ⟶ j') (g : j' ⟶ j'') :
    CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A S) (F.map (f ≫ g)).hom).toRingHom =
      CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom).toRingHom ≫
        CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id A S) (F.map g).hom).toRingHom := by
  -- Proof comment: base change commutes with composition on the right tensor factor.
  rw [← CommRingCat.ofHom_comp]
  ext
  · simp
  · simp [Functor.map_comp, Algebra.TensorProduct.map_comp]

/-- Helper for Lemma 10.127.7: the literal tensor-stage diagram `j ↦ S ⊗[A] F.obj j`. -/
abbrev tensor_base_change_diagram
    (S : Type u) [CommRing S] [Algebra A S] :
    J ⥤ CommRingCat where
  obj j := CommRingCat.of (S ⊗[A] ↑(F.obj j))
  map f := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A S) (F.map f).hom).toRingHom
  map_id := tensor_base_change_diagram_map_id (A := A) (F := F) S
  map_comp := tensor_base_change_diagram_map_comp (A := A) (F := F) S

/-- Helper for Lemma 10.127.7: the backend tensor cocone obtained before replacing the proof-facing
diagram by literal tensor products. -/
abbrev tensor_base_change_backend_under_cocone
    (S : Type u) [CommRing S] [Algebra A S] :
    Cocone (tensor_base_change_backend_under_diagram (A := A) (J := J) F S) :=
  (CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).mapCocone <|
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor).mapCocone (colimit.cocone F)

/-- Helper for Lemma 10.127.7: the left tensor inclusion is natural in the stage variable. -/
lemma tensor_base_change_left_natTrans_naturality
    (S : Type u) [CommRing S] [Algebra A S]
    {j j' : J} (f : j ⟶ j') :
    CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(F.obj j)) ≫
      (tensor_base_change_diagram (A := A) (J := J) F S).map f =
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(F.obj j')) := by
  -- Proof comment: tensor base change only changes the right factor, so the left inclusion is
  -- preserved by every transition map.
  ext x
  simp [tensor_base_change_diagram]

/-- Helper for Lemma 10.127.7: the left tensor-factor maps into the literal tensor-stage diagram. -/
abbrev tensor_base_change_left_natTrans
    (S : Type u) [CommRing S] [Algebra A S] :
    (Functor.const J).obj (CommRingCat.of S) ⟶ tensor_base_change_diagram (A := A) (J := J) F S :=
  { app := fun j ↦
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(F.obj j))
    naturality := fun {_ _} f ↦
      (tensor_base_change_left_natTrans_naturality (A := A) (F := F) S f).symm }

/-- Helper for Lemma 10.127.7: the scalar maps `A → S ⊗[A] F.obj j` form a natural
transformation. -/
abbrev tensor_base_change_scalar_natTrans
    (S : Type u) [CommRing S] [Algebra A S] :
    (Functor.const J).obj (CommRingCat.of A) ⟶ tensor_base_change_diagram (A := A) (J := J) F S :=
  { app := fun j ↦
      CommRingCat.ofHom (algebraMap A S) ≫
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(F.obj j))
    naturality := fun {_ _} f ↦ sorry }

/-- Helper for Lemma 10.127.7: the colimit tensor maps form a cocone on the literal tensor-stage
diagram. -/
lemma tensor_base_change_cocone_naturality
    (S : Type u) [CommRing S] [Algebra A S]
    {j j' : J} (f : j ⟶ j') :
    (tensor_base_change_diagram (A := A) (J := J) F S).map f ≫
        CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j').hom).toRingHom =
      CommRingCat.ofHom
        (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom).toRingHom := by
  -- Proof comment: the cocone relations are preserved by tensoring with the fixed left factor `S`.
  rw [← CommRingCat.ofHom_comp]
  ext
  · simp
  · simp [tensor_base_change_diagram, Algebra.TensorProduct.map_comp]

/-- Helper for Lemma 10.127.7: the canonical cocone on the literal tensor-stage diagram with point
`S ⊗[A] colimit F`. -/
abbrev tensor_base_change_cocone
    (S : Type u) [CommRing S] [Algebra A S] :
  Cocone (tensor_base_change_diagram (A := A) (J := J) F S) where
  pt := CommRingCat.of (S ⊗[A] ↑(colimit F))
  ι :=
    { app := fun j ↦
        CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom).toRingHom
      naturality := fun {_ _} f ↦ sorry }

/-- Helper for Lemma 10.127.7: the literal tensor-stage diagram lifted to the under category via
its common left tensor-factor maps. -/
abbrev tensor_base_change_lifted_under_diagram
    (S : Type u) [CommRing S] [Algebra A S] :
    J ⥤ Under (CommRingCat.of S) :=
  Under.lift
    (tensor_base_change_diagram (A := A) (J := J) F S)
    (tensor_base_change_left_natTrans (A := A) (F := F) S)

/-- Helper for Lemma 10.127.7: the colimit tensor cocone lifts to the under category using the
left tensor inclusion into `S ⊗[A] colimit F`. -/
lemma tensor_base_change_lifted_under_cocone_factor
    (S : Type u) [CommRing S] [Algebra A S] (j : J) :
    (tensor_base_change_left_natTrans (A := A) (F := F) S).app j ≫
        (tensor_base_change_cocone (A := A) (J := J) F S).ι.app j =
      CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(colimit F)) := by
  -- Route correction: previous attempts compared the backend `Under` cocone too early.
  -- Here we first normalize the literal tensor leg to the common left inclusion.
  -- Proof comment: after passing to underlying ring homs, the goal is exactly the previously
  -- proved `AlgHom` identity rewritten via `AlgHom.toRingHom`.
  apply CommRingCat.hom_ext
  change
    ((Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(F.obj j))) =
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(colimit F))
  change
    ((Algebra.TensorProduct.map (AlgHom.id A S) (colimit.ι F j).hom).comp
      Algebra.TensorProduct.includeLeft).toRingHom =
        (Algebra.TensorProduct.includeLeft :
          S →ₐ[A] S ⊗[A] ↑(colimit F)).toRingHom
  rw [Algebra.TensorProduct.map_comp_includeLeft
    (R := A) (S := A) (A := S) (B := ↑(F.obj j))
    (C := S) (D := ↑(colimit F))]
  simp

/-- Helper for Lemma 10.127.7: the literal tensor cocone lifted to the under category. -/
abbrev tensor_base_change_lifted_under_cocone
    (S : Type u) [CommRing S] [Algebra A S] :
    Cocone (tensor_base_change_lifted_under_diagram (A := A) (J := J) F S) :=
  Under.liftCocone
    (tensor_base_change_diagram (A := A) (J := J) F S)
    (tensor_base_change_left_natTrans (A := A) (F := F) S)
    (tensor_base_change_cocone (A := A) (J := J) F S)
    (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑(colimit F)))
    (tensor_base_change_lifted_under_cocone_factor (A := A) (F := F) S)

/-- Helper for Lemma 10.127.7: forgetting the lifted `Under` cocone recovers the literal tensor
cocone. -/
lemma tensor_base_change_forget_lifted_under_cocone_eq
    (S : Type u) [CommRing S] [Algebra A S] :
    (Under.forget (CommRingCat.of S)).mapCocone
        (tensor_base_change_lifted_under_cocone (A := A) (J := J) F S) =
      tensor_base_change_cocone (A := A) (J := J) F S := by
  -- Proof comment: `Under.forget` drops exactly the extra left-structure and leaves the ring-level
  -- cocone untouched.
  rfl

end
