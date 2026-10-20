module

public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import stacks_project.Chap10.Lemma_10_127_7.TensorDiagram

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

/-- Helper for Lemma 10.127.7: transporting the original colimit cocone across the equivalence
`CommAlgCat A ≃ Under (CommRingCat.of A)` preserves the colimit property. -/
noncomputable abbrev tensor_base_change_equivalence_under_cocone_isColimit :
    IsColimit
      (((commAlgCatEquivUnder (CommRingCat.of A)).functor).mapCocone (colimit.cocone F)) := by
  -- Proof comment: equivalences preserve all colimits, so this first source-faithful transport
  -- is immediate.
  exact
    isColimitOfPreserves
      ((commAlgCatEquivUnder (CommRingCat.of A)).functor)
      (colimit.isColimit F)

/-- Helper for Lemma 10.127.7: tensoring the `Under`-valued diagram with `S` preserves the
filtered colimit because `CommRingCat.tensorProd` is a left adjoint via pushout. -/
noncomputable abbrev tensor_base_change_backend_under_cocone_isColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    IsColimit (tensor_base_change_backend_under_cocone (A := A) (J := J) F S) := by
  -- Route correction: instead of asking instance search to synthesize colimit preservation for
  -- `tensorProd` directly, transport the known left-adjoint structure along
  -- `tensorProdIsoPushout`.
  let _ :
      (CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).IsLeftAdjoint :=
    Functor.isLeftAdjoint_of_iso
      (CommRingCat.tensorProdIsoPushout (CommRingCat.of A) (CommRingCat.of S)).symm
  -- Proof comment: left adjoints preserve all colimits, so the backend tensor cocone stays
  -- colimiting after this second source-faithful transport.
  exact isColimitOfPreserves
    (CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S))
    (tensor_base_change_equivalence_under_cocone_isColimit (A := A) (J := J) F)

/-- Helper for Lemma 10.127.7: the right object of the `Under`-object corresponding to an
`A`-algebra is the original commutative ring. -/
lemma tensor_base_change_backend_under_right_eq
    (T : CommAlgCat.{u} A) :
    (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right = CommRingCat.of ↑T := sorry

/-- Helper for Lemma 10.127.7: the right object of the backend `Under`-object is canonically
`A`-algebra equivalent to the original algebra. -/
noncomputable def tensor_base_change_backend_under_right_algEquiv
    (T : CommAlgCat.{u} A) :
    letI : Algebra A (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right :=
      ((((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).hom).hom.toAlgebra
    ↑(((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right ≃ₐ[A] ↑T := by
  letI : Algebra A (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right :=
    ((((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).hom).hom.toAlgebra
  have hT :
      (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right = CommRingCat.of ↑T :=
    tensor_base_change_backend_under_right_eq (A := A) T
  -- Proof comment: after rewriting the right object back to `T`, the desired algebra equivalence
  -- is just the identity.
  cases hT
  refine
    { toRingEquiv := RingEquiv.refl _
      commutes' := ?_ }
  intro a
  rfl

/-- Helper for Lemma 10.127.7: the canonical algebra equivalence from the backend right object to
the original algebra acts as the identity on elements. -/
@[simp] lemma tensor_base_change_backend_under_right_algEquiv_apply
    (T : CommAlgCat.{u} A)
    (x : (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T).right) :
    tensor_base_change_backend_under_right_algEquiv (A := A) T x = x := sorry

/-- Helper for Lemma 10.127.7: for a fixed backend `Under`-object, forgetting after tensoring with
`S` produces the literal tensor-product stage. -/
lemma tensor_base_change_backend_forget_obj_eq_under
    (S : Type u) [CommRing S] [Algebra A S]
    (U : Under (CommRingCat.of A)) :
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    (Under.forget (CommRingCat.of S)).obj
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).obj U) =
      CommRingCat.of (S ⊗[A] U.right) := sorry

/-- Helper for Lemma 10.127.7: the backend `Under`-object attached to an `A`-algebra is the
canonical object `A → T`. -/
lemma tensor_base_change_backend_under_obj_eq_mkUnder
    (T : CommAlgCat.{u} A) :
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T =
      CommRingCat.mkUnder (CommRingCat.of A) ↑T := sorry

/-- Helper for Lemma 10.127.7: the backend map attached to an algebra morphism is literally the
same morphism viewed in the under category. -/
@[simp] lemma tensor_base_change_backend_under_map_eq_toUnder
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    ((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g = g.hom.toUnder := sorry

/-- Helper for Lemma 10.127.7: specializing the backend-forget object equality to the under-object
coming from an `A`-algebra exposes the intermediate tensor stage `S ⊗[A] U.right`. -/
lemma tensor_base_change_backend_forget_obj_eq_backend_right
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    (Under.forget (CommRingCat.of S)).obj
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).obj U) =
      CommRingCat.of (S ⊗[A] U.right) := sorry

/-- Helper for Lemma 10.127.7: in the pushout model for the backend tensor stage, the left
generator map from `S` is exactly the canonical left tensor inclusion. -/
lemma tensor_base_change_backend_pushout_inv_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) := sorry

/-- Helper for Lemma 10.127.7: in the pushout model for the backend tensor stage, the right
generator map from the backend algebra is exactly the canonical right tensor inclusion. -/
lemma tensor_base_change_backend_pushout_inv_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right =
      CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).toRingHom) := sorry

/-- Helper for Lemma 10.127.7: the final `eqToHom` transport in the forgotten backend tensor stage
identifies the left tensor generator with the literal pushout-model left generator map. -/
lemma tensor_base_change_backend_eqToHom_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm =
      pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := sorry

/-- Helper for Lemma 10.127.7: the final `eqToHom` transport in the forgotten backend tensor stage
identifies the right tensor generator with the literal pushout-model right generator map. -/
lemma tensor_base_change_backend_eqToHom_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).toRingHom) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := sorry

/-- Helper for Lemma 10.127.7: the forgotten backend tensor stage is canonically isomorphic to the
literal tensor stage used in the source proof. -/
noncomputable def tensor_base_change_backend_forget_obj_iso
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    (Under.forget (CommRingCat.of S)).obj
      ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).obj
        (((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T)) ≅
      CommRingCat.of (S ⊗[A] ↑T) := by
  let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor).obj T
  letI : Algebra A U.right := U.hom.hom.toAlgebra
  let e : CommRingCat.of (S ⊗[A] U.right) ≅ CommRingCat.of (S ⊗[A] ↑T) :=
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : S ≃ₐ[A] S)
      (tensor_base_change_backend_under_right_algEquiv (A := A) T)).toRingEquiv.toCommRingCatIso
  -- Proof comment: first identify the forgotten backend stage with `S ⊗[A] U.right`, then use
  -- the canonical `A`-algebra equivalence `U.right ≃ₐ[A] T` on the right tensor factor.
  exact eqToIso (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U) ≪≫ e

/-- Helper for Lemma 10.127.7: before the final object-transport, the right-factor comparison
isomorphism fixes the left tensor generator. -/
lemma tensor_base_change_backend_congr_symm_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫
        CommRingCat.ofHom
          ((Algebra.TensorProduct.congr
            (AlgEquiv.refl : S ≃ₐ[A] S)
            (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm.toRingHom) =
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] U.right) := sorry

/-- Helper for Lemma 10.127.7: before the final object-transport, the right tensor generator is
carried along the inverse of the backend-right algebra equivalence. -/
lemma tensor_base_change_backend_congr_symm_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫
        CommRingCat.ofHom
          ((Algebra.TensorProduct.congr
            (AlgEquiv.refl : S ≃ₐ[A] S)
            (tensor_base_change_backend_under_right_algEquiv (A := A) T)).symm.toRingHom) =
      CommRingCat.ofHom
        ((((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).comp
            (tensor_base_change_backend_under_right_algEquiv (A := A) T).symm)).toRingHom) := sorry

/-- Helper for Lemma 10.127.7: the inverse of the stage comparison isomorphism carries the left
tensor generator to the pushout-model left generator map. -/
lemma tensor_base_change_backend_forget_obj_iso_inv_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[A] ↑T) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv =
      pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := sorry

/-- Helper for Lemma 10.127.7: the inverse of the stage comparison isomorphism carries the right
tensor generator to the pushout-model right generator map. -/
lemma tensor_base_change_backend_congr_symm_comp_includeRight_transport
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((((Algebra.TensorProduct.includeRight : U.right →ₐ[A] S ⊗[A] U.right).comp
            (tensor_base_change_backend_under_right_algEquiv (A := A) T).symm)).toRingHom) ≫
        eqToHom (tensor_base_change_backend_forget_obj_eq_under (A := A) (S := S) U).symm =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := sorry

/-- Helper for Lemma 10.127.7: the inverse of the stage comparison isomorphism carries the right
tensor generator to the pushout-model right generator map. -/
lemma tensor_base_change_backend_forget_obj_iso_inv_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    (T : CommAlgCat.{u} A) :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    CommRingCat.ofHom
        ((Algebra.TensorProduct.includeRight : ↑T →ₐ[A] S ⊗[A] ↑T).toRingHom) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv =
      pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right := sorry

/-- Helper for Lemma 10.127.7: conjugating the backend tensor-transition map by the pushout-model
comparison isomorphisms identifies it with the literal pushout transition map. -/
lemma tensor_base_change_pushout_map_conj
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
          (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := sorry

/-- Helper for Lemma 10.127.7: the commutativity witness defining the pushout transition map
attached to an `A`-algebra morphism `g`. -/
lemma tensor_base_change_pushout_map_desc_comm
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    U.hom ≫
        (CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S))) =
      CommRingCat.ofHom (algebraMap A S) ≫
        pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) := sorry

/-- Helper for Lemma 10.127.7: the right component of `Under.pushout.map` is the literal
`pushout.desc` on the pushout model. -/
lemma tensor_base_change_pushout_map_right_eq_desc
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    ((Under.pushout (CommRingCat.ofHom (algebraMap A S))).map
      (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g)).right =
      pushout.desc
        (CommRingCat.ofHom g.hom.toRingHom ≫
          pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)))
        (pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)))
        (tensor_base_change_pushout_map_desc_comm (A := A) (S := S) g) := sorry

/-- Helper for Lemma 10.127.7: the pushout-model transition map fixes the left tensor generator. -/
lemma tensor_base_change_pushout_map_comp_includeLeft
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    pushout.inr U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      pushout.inr U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := sorry

/-- Helper for Lemma 10.127.7: the pushout-model transition map sends the right tensor generator
through the algebra map `g`. -/
lemma tensor_base_change_pushout_map_comp_includeRight
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    let U := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T)
    let U' := ((commAlgCatEquivUnder (CommRingCat.of A)).functor.obj T')
    letI : Algebra A U.right := U.hom.hom.toAlgebra
    letI : Algebra A U'.right := U'.hom.hom.toAlgebra
    pushout.inl U.hom (CommRingCat.ofHom (algebraMap A S)) ≫
        (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U).inv.right ≫
        ((Under.forget (CommRingCat.of S)).map
          ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) =
      CommRingCat.ofHom g.hom.toRingHom ≫
        pushout.inl U'.hom (CommRingCat.ofHom (algebraMap A S)) ≫
          (CommRingCat.tensorProdObjIsoPushoutObj (CommRingCat.of S) U').inv.right := sorry

/-- Helper for Lemma 10.127.7: after identifying the backend tensor stages with the literal tensor
products by the canonical stage isomorphisms, the forgotten backend tensor map is exactly the
literal tensor map on the right factor. -/
lemma tensor_base_change_backend_forget_hom_conj_eq_literal
    (S : Type u) [CommRing S] [Algebra A S]
    {T T' : CommAlgCat.{u} A} (g : T ⟶ T') :
    (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T).inv ≫
        ((Under.forget (CommRingCat.of S)).map
        ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of S)).map
            (((commAlgCatEquivUnder (CommRingCat.of A)).functor).map g))) ≫
        (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) T').hom =
      CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A S) g.hom).toRingHom := sorry

/-- Helper for Lemma 10.127.7: after forgetting the backend `Under` proof data, the transported
tensor diagram is canonically isomorphic to the literal tensor-stage diagram used in the source
proof. -/
abbrev tensor_base_change_backend_forget_diagram_iso
    (S : Type u) [CommRing S] [Algebra A S] :
    (tensor_base_change_backend_under_diagram (A := A) (J := J) F S) ⋙
        Under.forget (CommRingCat.of S) ≅
      tensor_base_change_diagram (A := A) (J := J) F S :=
  by
    -- Proof comment: the components are the canonical stage comparison isomorphisms.
    refine NatIso.ofComponents
      (fun j ↦ tensor_base_change_backend_forget_obj_iso (A := A) (S := S) (F.obj j))
      (fun {_ _} f ↦ sorry)

/-- Helper for Lemma 10.127.7: forgetting the backend tensor cocone matches the literal tensor
cocone after precomposing along the backend-forget diagram isomorphism. -/
noncomputable abbrev tensor_base_change_backend_forget_cocone_iso_ext
    (S : Type u) [CommRing S] [Algebra A S] :
    (Under.forget (CommRingCat.of S)).mapCocone
        (tensor_base_change_backend_under_cocone (A := A) (J := J) F S) ≅
      (Cocone.precompose
        (tensor_base_change_backend_forget_diagram_iso
          (A := A) (J := J) (F := F) S).hom).obj
        (tensor_base_change_cocone (A := A) (J := J) F S) := by
  -- Proof comment: once the backend/literal conjugation is available for every structure map
  -- `colimit.ι F j`, the cocone comparison is a direct `Cocone.ext`.
  refine Cocone.ext
    (tensor_base_change_backend_forget_obj_iso (A := A) (S := S) (colimit F))
    (fun j ↦ sorry)

/-- Helper for Lemma 10.127.7: the tensor-base-change cocone is colimiting. -/
noncomputable abbrev tensor_base_change_cocone_isColimit
    (S : Type u) [CommRing S] [Algebra A S] :
    IsColimit (tensor_base_change_cocone (A := A) (J := J) F S) :=
  by
    -- Route correction: instead of transporting inside `Under`, first forget the backend cocone
    -- to plain commutative rings, where the comparison to the literal tensor cocone is stable.
    -- Proof comment: first forget the proven backend colimit cocone, then transport that
    -- colimit witness across the explicit cocone isomorphism to the precomposed literal cocone,
    -- and finally remove the precomposition via the diagram isomorphism.
    let hc_under := tensor_base_change_backend_under_cocone_isColimit
      (A := A) (J := J) F S
    let hc_forget := isColimitOfPreserves (Under.forget (CommRingCat.of S)) hc_under
    let hc_pre :
        IsColimit
          ((Cocone.precompose
            (tensor_base_change_backend_forget_diagram_iso
              (A := A) (J := J) (F := F) S).hom).obj
            (tensor_base_change_cocone (A := A) (J := J) F S)) :=
      IsColimit.ofIsoColimit hc_forget
        (tensor_base_change_backend_forget_cocone_iso_ext
          (A := A) (J := J) (F := F) S)
    exact
      (IsColimit.precomposeHomEquiv
        (tensor_base_change_backend_forget_diagram_iso
          (A := A) (J := J) (F := F) S)
        (tensor_base_change_cocone (A := A) (J := J) F S)).1 hc_pre

/-- Helper for Lemma 10.127.7: a filtered index category has an object, which is the only extra
input needed by `Under.isColimitLiftCocone`. -/
lemma tensor_base_change_index_nonempty : Nonempty J := sorry

end
