/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Composition
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.IndexedFunctor.Coherence.Isomorphism

/-!
# Coherence for indexed-functor composition
-/

@[expose] public section

universe uC vC uD vD uE vE uI vI uJ vJ uF vF uG vG uH vH uM vM uN vN

namespace CategoryTheory

open Opposite
open scoped CategoryTheory.Bicategory

namespace Pseudofunctor.LocallyDiscreteOpToCat

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

namespace IndexedFunctor

variable {u : C ⥤ D}
variable {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{vF, uF}}
variable {G : LocallyDiscrete Dᵒᵖ ⥤ᵖ Cat.{vG, uG}}

/-- The component associator between the two bracketings of a composite of three indexed
functors. -/
noncomputable def compAssocIsoApp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {I : Type uI} [Category.{vI} I] {w : E ⥤ I}
    {M : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM, uM}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    (T : IndexedFunctor w L M) (U : C) :
    ((H.comp K).comp T).app U ≅ (H.comp (K.comp T)).app U :=
  Functor.associator (H.app U) (K.app (u.obj U))
    (T.app (v.obj (u.obj U)))

/-- Component associators for three indexed functors commute with base reindexing. -/
theorem compAssocIso_naturality
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {I : Type uI} [Category.{vI} I] {w : E ⥤ I}
    {M : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM, uM}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    (T : IndexedFunctor w L M)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (((H.comp K).comp T).naturality f).hom.app x ≫
        (M.map (((u ⋙ v) ⋙ w).map f).op.toLoc).toFunctor.map
          ((compAssocIsoApp H K T U).hom.app x) =
      (compAssocIsoApp H K T V).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        ((H.comp (K.comp T)).naturality f).hom.app x := sorry

/-- The two bracketings of a composite of three indexed functors are canonically isomorphic. -/
noncomputable def compAssocIso
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {I : Type uI} [Category.{vI} I] {w : E ⥤ I}
    {M : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM, uM}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    (T : IndexedFunctor w L M) :
    (H.comp K).comp T ≅ H.comp (K.comp T) :=
  IndexedFunctor.mkIso
    (compAssocIsoApp H K T)
    (fun f x ↦ compAssocIso_naturality H K T f x)

/-- Components of the indexed associator are ordinary functor associators. -/
@[simp]
theorem compAssocIso_isoApp
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {I : Type uI} [Category.{vI} I] {w : E ⥤ I}
    {M : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM, uM}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    (T : IndexedFunctor w L M) (U : C) :
    isoApp (compAssocIso H K T) U = compAssocIsoApp H K T U := sorry

/-- The component left unitor for composition with the identity indexed functor. -/
noncomputable def idCompIsoApp
    (H : IndexedFunctor u F G) (U : C) :
    ((id F).comp H).app U ≅ H.app U :=
  Functor.leftUnitor (H.app U)

/-- Component left unitors for indexed functors commute with base reindexing. -/
theorem idCompIso_naturality
    (H : IndexedFunctor u F G)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    (((id F).comp H).naturality f).hom.app x ≫
        (G.map (u.map f).op.toLoc).toFunctor.map
          ((idCompIsoApp H U).hom.app x) =
      (idCompIsoApp H V).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (H.naturality f).hom.app x := sorry

/-- Composition with the identity indexed functor on the source is canonically isomorphic to
the original indexed functor. -/
noncomputable def idCompIso (H : IndexedFunctor u F G) :
    (id F).comp H ≅ H :=
  IndexedFunctor.mkIso
    (idCompIsoApp H)
    (fun f x ↦ idCompIso_naturality H f x)

/-- Components of the indexed left unitor are ordinary functor left unitors. -/
@[simp]
theorem idCompIso_isoApp (H : IndexedFunctor u F G) (U : C) :
    isoApp (idCompIso H) U = idCompIsoApp H U := sorry

/-- The component right unitor for composition with the identity indexed functor. -/
noncomputable def compIdIsoApp
    (H : IndexedFunctor u F G) (U : C) :
    (H.comp (id G)).app U ≅ H.app U :=
  Functor.rightUnitor (H.app U)

/-- Component right unitors for indexed functors commute with base reindexing. -/
theorem compIdIso_naturality
    (H : IndexedFunctor u F G)
    {U V : C} (f : V ⟶ U)
    (x : F.obj (LocallyDiscrete.mk (Opposite.op U))) :
    ((H.comp (id G)).naturality f).hom.app x ≫
        (G.map (u.map f).op.toLoc).toFunctor.map
          ((compIdIsoApp H U).hom.app x) =
      (compIdIsoApp H V).hom.app
          ((F.map f.op.toLoc).toFunctor.obj x) ≫
        (H.naturality f).hom.app x := sorry

/-- Composition with the identity indexed functor on the target is canonically isomorphic to
the original indexed functor. -/
noncomputable def compIdIso (H : IndexedFunctor u F G) :
    H.comp (id G) ≅ H :=
  IndexedFunctor.mkIso
    (compIdIsoApp H)
    (fun f x ↦ compIdIso_naturality H f x)

/-- Components of the indexed right unitor are ordinary functor right unitors. -/
@[simp]
theorem compIdIso_isoApp (H : IndexedFunctor u F G) (U : C) :
    isoApp (compIdIso H) U = compIdIsoApp H U := sorry

/-- The indexed associator is natural simultaneously in modifications of all three factors. -/
theorem compAssocIso_hom_naturality
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {I : Type uI} [Category.{vI} I] {w : E ⥤ I}
    {M : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM, uM}}
    {H₁ H₂ : IndexedFunctor u F G} (α : H₁ ⟶ H₂)
    {K₁ K₂ : IndexedFunctor v G L} (β : K₁ ⟶ K₂)
    {T₁ T₂ : IndexedFunctor w L M} (γ : T₁ ⟶ T₂) :
    compHom (compHom α β) γ ≫ (compAssocIso H₂ K₂ T₂).hom =
      (compAssocIso H₁ K₁ T₁).hom ≫ compHom α (compHom β γ) := sorry

/-- The indexed left unitor is natural in modifications. -/
theorem idCompIso_hom_naturality
    {H K : IndexedFunctor u F G} (α : H ⟶ K) :
    precompHom (id F) α ≫ (idCompIso K).hom =
      (idCompIso H).hom ≫ α := sorry

variable (u F G) in
/-- Left composition by the identity indexed functor is naturally isomorphic to the identity
functor on the corresponding category of indexed functors.  The reindexing functor and both
indexed pseudofunctors are explicit because this natural isomorphism has no value input from
which Lean can recover them. -/
noncomputable def idCompNatIso :
    precomp u G (id F) ≅
      𝟭 (IndexedFunctor u F G) :=
  NatIso.ofComponents
    idCompIso
    (fun α ↦ idCompIso_hom_naturality α)

/-- Components of the indexed left-unitor natural isomorphism are the canonical indexed left
unitors. -/
@[simp]
theorem idCompNatIso_app (H : IndexedFunctor u F G) :
    (idCompNatIso u F G).app H = idCompIso H := sorry

/-- The indexed right unitor is natural in modifications. -/
theorem compIdIso_hom_naturality
    {H K : IndexedFunctor u F G} (α : H ⟶ K) :
    postcompHom α (id G) ≫ (compIdIso K).hom =
      (compIdIso H).hom ≫ α := sorry

variable (u F G) in
/-- Right composition by the identity indexed functor is naturally isomorphic to the identity
functor on the corresponding category of indexed functors.  The reindexing functor and both
indexed pseudofunctors are explicit because this natural isomorphism has no value input from
which Lean can recover them. -/
noncomputable def compIdNatIso :
    postcomp u F (id G) ≅
      𝟭 (IndexedFunctor u F G) :=
  NatIso.ofComponents
    compIdIso
    (fun α ↦ compIdIso_hom_naturality α)

/-- Components of the indexed right-unitor natural isomorphism are the canonical indexed right
unitors. -/
@[simp]
theorem compIdNatIso_app (H : IndexedFunctor u F G) :
    (compIdNatIso u F G).app H = compIdIso H := sorry

/-- The associators for composition of indexed functors satisfy the pentagon identity. -/
theorem compAssocIso_pentagon
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    {I : Type uI} [Category.{vI} I] {w : E ⥤ I}
    {M : LocallyDiscrete Iᵒᵖ ⥤ᵖ Cat.{vM, uM}}
    {J : Type uJ} [Category.{vJ} J] {z : I ⥤ J}
    {N : LocallyDiscrete Jᵒᵖ ⥤ᵖ Cat.{vN, uN}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L)
    (T : IndexedFunctor w L M) (S : IndexedFunctor z M N) :
    (compAssocIso (H.comp K) T S).hom ≫
        (compAssocIso H K (T.comp S)).hom =
      postcompHom (compAssocIso H K T).hom S ≫
        (compAssocIso H (K.comp T) S).hom ≫
          precompHom H (compAssocIso K T S).hom := sorry

/-- The associator and unitors for composition of indexed functors satisfy the triangle
identity. -/
theorem compAssocIso_triangle
    {E : Type uE} [Category.{vE} E] {v : D ⥤ E}
    {L : LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat.{vH, uH}}
    (H : IndexedFunctor u F G) (K : IndexedFunctor v G L) :
    (compAssocIso H (id G) K).hom ≫
        precompHom H (idCompIso K).hom =
      postcompHom (compIdIso H).hom K := sorry


end IndexedFunctor

end Pseudofunctor.LocallyDiscreteOpToCat

end CategoryTheory
