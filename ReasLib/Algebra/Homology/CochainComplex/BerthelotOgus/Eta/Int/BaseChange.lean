/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.BaseChange
public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int

/-!
# Flat base change for the integer-indexed Berthelot-Ogus eta operator

The degreewise comparison is defined for every ring map as soon as the source and target
complexes carry the regularity needed by the divided-differential model.  Flatness is used only
to produce the target regularity and prove that the resulting canonical comparison is an
isomorphism.

@stack 0GSR
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex

noncomputable section

universe u v w

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]

namespace BaseChange

/-- Scalar extension on integer-indexed cochain complexes. -/
@[stacks 0GSR "scalar extension of integer-indexed cochain complexes"]
noncomputable abbrev scalarExtension :=
  (ModuleCat.extendScalars.{u, v, max v w}
    (algebraMap A B)).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ambient degree map from the scalar extension of an integer eta term to the scalar
extension of the corresponding term of the original complex. -/
@[stacks 0GSR "ambient integer eta base-change map"]
noncomputable def inclusionLinear
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K i)) →ₗ[B]
      (ModuleCat.extendScalars (algebraMap A B)).obj (K.X i) :=
  ((ModuleCat.extendScalars (algebraMap A B)).map
    (ModuleCat.ofHom (term f K i).subtype)).hom

/-- The ambient scalar-extension map sends an extended integer eta term into the eta term of
the scalar-extended complex. -/
theorem inclusion_mem
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ)
    (x : (ModuleCat.extendScalars (algebraMap A B)).obj
      (ModuleCat.of A (term f K i))) :
    inclusionLinear (B := B) f K i x ∈
      term (algebraMap A B f) ((scalarExtension (A := A) (B := B)).obj K) i := sorry

/-- The canonical degree map from the scalar extension of an integer eta term to the
corresponding eta term after scalar extension. -/
@[stacks 0GSR "degreewise integer eta base-change map"]
noncomputable def termLinear
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K i)) →ₗ[B]
      term (algebraMap A B f) ((scalarExtension (A := A) (B := B)).obj K) i :=
  (inclusionLinear (B := B) f K i).codRestrict _ (inclusion_mem (B := B) f K i)

/-- The bundled canonical degree comparison for integer eta terms. -/
@[stacks 0GSR "bundled degreewise integer eta comparison"]
noncomputable def termHom
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ) :
    (ModuleCat.extendScalars (algebraMap A B)).obj
        (ModuleCat.of A (term f K i)) ⟶
      ModuleCat.of B
        (term (algebraMap A B f) ((scalarExtension (A := A) (B := B)).obj K) i) :=
  ConcreteCategory.ofHom (C := ModuleCat B) (termLinear (B := B) f K i)

/-- The underlying linear map of the bundled degree comparison is `termLinear`. -/
@[simp]
theorem termHom_hom
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ) (i : ℤ) :
    (termHom (B := B) f K i).hom = termLinear (B := B) f K i := sorry

end BaseChange

/-- Flat scalar extension preserves termwise regularity for an integer-indexed cochain
complex. -/
@[stacks 0GSR "termwise regularity under flat base change"]
theorem IsTermwiseTorsionFree.scalarExtension [Module.Flat A B] {f : A}
    {K : CochainComplex (ModuleCat.{max v w} A) ℤ}
    (hK : IsTermwiseTorsionFree f K) :
    IsTermwiseTorsionFree (algebraMap A B f)
      ((BaseChange.scalarExtension (A := A) (B := B)).obj K) := sorry

namespace BaseChange

/-- Flat scalar extension lifts the bundled integer regular domain to the corresponding domain
over the target ring. -/
@[stacks 0GSR "flat scalar extension of the bundled integer eta domain"]
noncomputable def domainScalarExtension [Module.Flat A B] (f : A) :
    Domain f ⥤ Domain (algebraMap A B f) :=
  ObjectProperty.lift _
    (ObjectProperty.ι
      (HomologicalComplex.IsTermwiseSMulRegular (r := f) :
        ObjectProperty (CochainComplex (ModuleCat.{max v w} A) ℤ)) ⋙
      scalarExtension (A := A) (B := B))
    (fun K ↦ IsTermwiseTorsionFree.scalarExtension (A := A) (B := B) K.property)

/-- The degreewise integer eta base-change maps commute with the divided differentials. -/
theorem termLinear_comm
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (hbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj K))
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    termHom (B := B) f K i ≫
        (eta (algebraMap A B f) ((scalarExtension (A := A) (B := B)).obj K) hbase).d i j =
      ((scalarExtension (A := A) (B := B)).obj (eta f K hK)).d i j ≫
        termHom (B := B) f K j := sorry

/-- The canonical map from the scalar extension of an integer eta complex to the integer eta
complex after scalar extension. -/
@[stacks 0GSR "integer-indexed Berthelot-Ogus eta base-change comparison"]
noncomputable def comparison
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (hbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj K)) :
    (scalarExtension (A := A) (B := B)).obj (eta f K hK) ⟶
      eta (algebraMap A B f) ((scalarExtension (A := A) (B := B)).obj K) hbase where
  f i := termHom (B := B) f K i
  comm' i j hij := termLinear_comm (B := B) f K hK hbase i j hij

/-- The same comparison with the source regularity carried by a bundled integer domain. -/
@[stacks 0GSR "integer eta comparison on the regular domain"]
noncomputable def comparisonOnDomain
    (f : A) (K : Domain f)
    (hbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj K.obj)) :
    (scalarExtension (A := A) (B := B)).obj (eta f K.obj K.property) ⟶
      eta (algebraMap A B f) ((scalarExtension (A := A) (B := B)).obj K.obj) hbase :=
  comparison (B := B) f K.obj K.property hbase

/-- The flat base-change comparison on bundled regular domains, with the target regularity
supplied by `domainScalarExtension`. -/
@[stacks 0GSR "flat integer eta comparison on the regular domain"]
noncomputable abbrev comparisonOnDomainFlat [Module.Flat A B]
    (f : A) (K : Domain f) :
    (scalarExtension (A := A) (B := B)).obj (eta f K.obj K.property) ⟶
      eta (algebraMap A B f)
        ((domainScalarExtension (A := A) (B := B) f).obj K).obj
        ((domainScalarExtension (A := A) (B := B) f).obj K).property :=
  comparisonOnDomain (B := B) f K
    ((domainScalarExtension (A := A) (B := B) f).obj K).property

/-- The component of the integer eta base-change comparison is the canonical degree
comparison. -/
@[simp]
theorem comparison_f
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (hbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj K)) (i : ℤ) :
    (comparison (B := B) f K hK hbase).f i = termHom (B := B) f K i := sorry

/-- The integer eta base-change comparison is natural in maps between complexes with the
specified source and target regularity. -/
theorem comparison_naturality
    (f : A) {K L : CochainComplex (ModuleCat.{max v w} A) ℤ} (φ : K ⟶ L)
    (hK : IsTermwiseTorsionFree f K) (hL : IsTermwiseTorsionFree f L)
    (hKbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj K))
    (hLbase : IsTermwiseTorsionFree (algebraMap A B f)
      ((scalarExtension (A := A) (B := B)).obj L)) :
    (scalarExtension (A := A) (B := B)).map (map f φ hK hL) ≫
        comparison (B := B) f L hL hLbase =
      comparison (B := B) f K hK hKbase ≫
        map (algebraMap A B f)
          ((scalarExtension (A := A) (B := B)).map φ) hKbase hLbase := sorry

/-- Naturality of the flat comparison on the bundled integer regular domain. -/
theorem comparisonFlat_naturality [Module.Flat A B]
    (f : A) {K L : Domain f} (φ : K ⟶ L) :
    (scalarExtension (A := A) (B := B)).map ((Int.functor f).map φ) ≫
        comparisonOnDomainFlat (B := B) f L =
      comparisonOnDomainFlat (B := B) f K ≫
        (Int.functor (algebraMap A B f)).map
          ((domainScalarExtension (A := A) (B := B) f).map φ) := sorry

/-- The flat integer eta base-change comparison as a natural transformation on the canonical
regular domain. -/
@[stacks 0GSR "natural flat base-change comparison for integer eta"]
noncomputable def comparisonFlat [Module.Flat A B] (f : A) :
    Int.functor f ⋙ scalarExtension (A := A) (B := B) ⟶
      domainScalarExtension (A := A) (B := B) f ⋙ Int.functor (algebraMap A B f) where
  app K := comparisonOnDomainFlat (B := B) f K
  naturality _ _ φ := comparisonFlat_naturality (B := B) f φ

/-- For a flat algebra, the canonical comparison for the integer-indexed eta operator is an
isomorphism. -/
@[stacks 0GSR "integer-indexed Berthelot-Ogus eta commutes with flat base change"]
instance comparisonIsIso [Module.Flat A B]
    (f : A) (K : CochainComplex (ModuleCat.{max v w} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    IsIso (comparison (B := B) f K hK
      (IsTermwiseTorsionFree.scalarExtension (A := A) (B := B) hK)) := sorry

/-- On the bundled regular domain, flat scalar extension makes the canonical comparison an
isomorphism without exposing either regularity proof. -/
@[stacks 0GSR "flat base change on the bundled integer eta domain"]
instance comparisonOnDomainIsIso [Module.Flat A B]
    (f : A) (K : Domain f) :
    IsIso (comparisonOnDomainFlat (A := A) (B := B) f K) := sorry

/-- Every component of the flat integer eta base-change natural transformation is an
isomorphism. -/
@[stacks 0GSR "componentwise flat integer eta base change"]
instance comparisonFlat_app_isIso [Module.Flat A B]
    (f : A) (K : Domain f) :
    IsIso ((comparisonFlat (B := B) f).app K) := sorry

end BaseChange

end CochainComplex.BerthelotOgus.Int
