module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.CategoryTheory.Limits.IsLimit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reasonable

/-!
# Quasi-compact absolutely quasi-separated approximations of algebraic spaces

Filtered étale-surjective approximations recover an algebraic space both as a colimit of
fppf sheaves and on sections over quasi-compact schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagram of sections of a diagram of algebraic spaces on a scheme `T` over `S`. -/
def sectionsDiagram {S : Scheme.{u}} {J : Type u} [Category J]
    (F : J ⥤ AlgebraicSpace S) (T : Over S) : J ⥤ Type u :=
  F ⋙ forgetToPresheaf ⋙ (evaluation (Over S)ᵒᵖ (Type u)).obj (op T)

/-- Evaluating `sectionsDiagram F T` at an index recovers the functor of points on `T`. -/
@[simp]
theorem sectionsDiagram_obj {S : Scheme.{u}} {J : Type u} [Category J]
    (F : J ⥤ AlgebraicSpace S) (T : Over S) (j : J) :
    (sectionsDiagram F T).obj j = (F.obj j).functorOfPoints.obj (op T) :=
  rfl

/-- The sections cocone of coprojections `ι` evaluated on a scheme `T` over `S`. -/
def sectionsCocone {S : Scheme.{u}} {J : Type u} [Category J] {X : AlgebraicSpace S}
    (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X) (T : Over S) :
    Cocone (sectionsDiagram F T) :=
  (forgetToPresheaf ⋙ (evaluation (Over S)ᵒᵖ (Type u)).obj (op T)).mapCocone
    (Cocone.mk X ι)

/-- The point of `sectionsCocone F ι T` is the functor of points of `X` on `T`. -/
@[simp]
theorem sectionsCocone_pt {S : Scheme.{u}} {J : Type u} [Category J] {X : AlgebraicSpace S}
    (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X) (T : Over S) :
    (sectionsCocone F ι T).pt = X.functorOfPoints.obj (op T) :=
  rfl

/-- A small filtered diagram of algebraic spaces with coprojections to `X` is a qcqs étale
approximation if the objects are quasi-compact and absolutely quasi-separated, the transitions and
coprojections are étale and surjective, the diagram is a colimit in the fppf sheaf category,
and sections on quasi-compact schemes over `S` recover the sections of `X`. -/
@[mk_iff]
structure IsQCQSEtaleApproximation {S : Scheme.{u}} {J : Type u} [SmallCategory J]
    [IsFiltered J] {X : AlgebraicSpace S} (F : J ⥤ AlgebraicSpace S)
    (ι : F ⟶ (Functor.const J).obj X) : Prop where
  /-- Each object of the diagram is a quasi-compact algebraic space. -/
  isQuasiCompact_obj (j : J) : IsQuasiCompact (F.obj j)
  /-- Each object of the diagram is an absolutely quasi-separated algebraic space. -/
  isQuasiSeparated_obj (j : J) : IsAbsolutelyQuasiSeparated (F.obj j)
  /-- Transition morphisms of the diagram are étale. -/
  etale_map {j j' : J} (f : j ⟶ j') : Etale (F.map f)
  /-- Transition morphisms of the diagram are surjective. -/
  surjective_map {j j' : J} (f : j ⟶ j') : Surjective (F.map f)
  /-- Coprojections to `X` are étale. -/
  etale_ι (j : J) : Etale (ι.app j)
  /-- Coprojections to `X` are surjective. -/
  surjective_ι (j : J) : Surjective (ι.app j)
  /-- The diagram is a colimit in the category of fppf sheaves on `Over S`. -/
  isColimit_toSheaf : Nonempty (IsColimit (toSheaf.mapCocone (Cocone.mk X ι)))
  /-- On every quasi-compact scheme `T` over `S`, sections of the diagram colimit to sections of
  `X`. -/
  isColimit_sections (T : Over S) [CompactSpace T.left] :
    Nonempty (IsColimit (sectionsCocone F ι T))

namespace IsQCQSEtaleApproximation

/-- Assemble a qcqs étale-surjective sheaf-colimit approximation from its named conditions. -/
def of {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    {X : AlgebraicSpace S} {F : J ⥤ AlgebraicSpace S}
    {ι : F ⟶ (Functor.const J).obj X}
    (isQuasiCompact_obj : ∀ j, IsQuasiCompact (F.obj j))
    (isQuasiSeparated_obj : ∀ j, IsAbsolutelyQuasiSeparated (F.obj j))
    (etale_map : ∀ {j j'} (f : j ⟶ j'), Etale (F.map f))
    (surjective_map : ∀ {j j'} (f : j ⟶ j'), Surjective (F.map f))
    (etale_ι : ∀ j, Etale (ι.app j))
    (surjective_ι : ∀ j, Surjective (ι.app j))
    (isColimit_toSheaf : Nonempty (IsColimit (toSheaf.mapCocone (Cocone.mk X ι))))
    (isColimit_sections :
      ∀ (T : Over S) [CompactSpace T.left], Nonempty (IsColimit (sectionsCocone F ι T))) :
    IsQCQSEtaleApproximation F ι where
  isQuasiCompact_obj := isQuasiCompact_obj
  isQuasiSeparated_obj := isQuasiSeparated_obj
  etale_map := etale_map
  surjective_map := surjective_map
  etale_ι := etale_ι
  surjective_ι := surjective_ι
  isColimit_toSheaf := isColimit_toSheaf
  isColimit_sections := isColimit_sections

/-- A qcqs étale approximation has quasi-compact absolutely quasi-separated objects, étale surjective
transitions and coprojections, a sheaf colimit, and a sections colimit on quasi-compact schemes. -/
theorem spec {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    {X : AlgebraicSpace S} (F : J ⥤ AlgebraicSpace S)
    (ι : F ⟶ (Functor.const J).obj X) (h : IsQCQSEtaleApproximation F ι) :
    (∀ j, IsQuasiCompact (F.obj j) ∧ IsAbsolutelyQuasiSeparated (F.obj j)) ∧
      (∀ {j j'} (f : j ⟶ j'), Etale (F.map f) ∧ Surjective (F.map f)) ∧
        (∀ j, Etale (ι.app j) ∧ Surjective (ι.app j)) ∧
          Nonempty (IsColimit (toSheaf.mapCocone (Cocone.mk X ι))) ∧
            ∀ (T : Over S), CompactSpace T.left →
              Nonempty (IsColimit (sectionsCocone F ι T)) :=
  ⟨fun j => ⟨h.isQuasiCompact_obj j, h.isQuasiSeparated_obj j⟩,
    fun f => ⟨h.etale_map f, h.surjective_map f⟩,
    fun j => ⟨h.etale_ι j, h.surjective_ι j⟩,
    h.isColimit_toSheaf, fun T hT => h.isColimit_sections T⟩

end IsQCQSEtaleApproximation

/-- A small filtered diagram of algebraic spaces with coprojections to `X` is a qcqs
local-isomorphism approximation if the objects are schemes and the transitions and coprojections
are local isomorphisms of schemes, in the representable sense on functors of points. -/
@[mk_iff]
structure IsQCQSLocalIsoApproximation {S : Scheme.{u}} {J : Type u} [SmallCategory J]
    [IsFiltered J] {X : AlgebraicSpace S} (F : J ⥤ AlgebraicSpace S)
    (ι : F ⟶ (Functor.const J).obj X) : Prop where
  /-- Each object of the diagram is a scheme. -/
  isScheme_obj (j : J) : IsScheme (F.obj j)
  /-- Transition morphisms are local isomorphisms of schemes, as representable morphisms of
  functors of points. -/
  isLocalIso_map {j j' : J} (f : j ⟶ j') :
    (MorphismProperty.over (@AlgebraicGeometry.IsLocalIso)).presheaf (F.map f)
  /-- Coprojections to `X` are local isomorphisms of schemes, as representable morphisms of
  functors of points. -/
  isLocalIso_ι (j : J) :
    (MorphismProperty.over (@AlgebraicGeometry.IsLocalIso)).presheaf (ι.app j)

namespace IsQCQSLocalIsoApproximation

/-- Assemble a qcqs local-isomorphism approximation from its named conditions. -/
def of {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    {X : AlgebraicSpace S} {F : J ⥤ AlgebraicSpace S}
    {ι : F ⟶ (Functor.const J).obj X}
    (isScheme_obj : ∀ j, IsScheme (F.obj j))
    (isLocalIso_map : ∀ {j j'} (f : j ⟶ j'),
      (MorphismProperty.over (@AlgebraicGeometry.IsLocalIso)).presheaf (F.map f))
    (isLocalIso_ι : ∀ j,
      (MorphismProperty.over (@AlgebraicGeometry.IsLocalIso)).presheaf (ι.app j)) :
    IsQCQSLocalIsoApproximation F ι where
  isScheme_obj := isScheme_obj
  isLocalIso_map := isLocalIso_map
  isLocalIso_ι := isLocalIso_ι

/-- A qcqs local-isomorphism approximation consists of schemes with local-isomorphism transitions
and coprojections. -/
theorem spec {S : Scheme.{u}} {J : Type u} [SmallCategory J] [IsFiltered J]
    {X : AlgebraicSpace S} (F : J ⥤ AlgebraicSpace S)
    (ι : F ⟶ (Functor.const J).obj X) (h : IsQCQSLocalIsoApproximation F ι) :
    (∀ j, IsScheme (F.obj j)) ∧
      (∀ {j j'} (f : j ⟶ j'),
        (MorphismProperty.over (@AlgebraicGeometry.IsLocalIso)).presheaf (F.map f)) ∧
        ∀ j, (MorphismProperty.over (@AlgebraicGeometry.IsLocalIso)).presheaf (ι.app j) :=
  ⟨h.isScheme_obj, h.isLocalIso_map, h.isLocalIso_ι⟩

end IsQCQSLocalIsoApproximation

/-- A quasi-compact reasonable algebraic space over an arbitrary scheme is a filtered
colimit of quasi-compact absolutely quasi-separated algebraic spaces in fppf sheaves and on
sections over quasi-compact schemes. Transitions and coprojections are étale and surjective.
When the target is a scheme, the same diagram consists of schemes and its transitions and
coprojections are local isomorphisms. -/
theorem exists_qcqs_etale_approximation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsReasonable X] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X),
      IsQCQSEtaleApproximation F ι ∧
        (IsScheme X → IsQCQSLocalIsoApproximation F ι) :=
  sorry

/-- A quasi-compact reasonable scheme, viewed as an algebraic space, admits a filtered
qcqs étale approximation whose objects are schemes and whose transitions and coprojections
are local isomorphisms. -/
theorem exists_qcqs_localIso_approximation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsReasonable X] [IsScheme X] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X),
      IsQCQSEtaleApproximation F ι ∧ IsQCQSLocalIsoApproximation F ι :=
by
  obtain ⟨J, hJ, hFiltered, F, ι, h, hScheme⟩ := exists_qcqs_etale_approximation X
  exact ⟨J, hJ, hFiltered, F, ι, h, hScheme inferInstance⟩

end AlgebraicGeometry.AlgebraicSpace
