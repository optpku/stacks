module

public import Mathlib.Algebra.Module.ZMod
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.FixedInterior
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ZMod
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Etale.FrobeniusStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback.ZMod

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.SchemeOverField
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {k : Type u} [Field k]
variable {p : ℕ} [Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]

/-- Extension by zero of a small-étale `ZMod (ℓ ^ n)`-module sheaf along the interior
immersion of a compactification. -/
def moduleExtensionByZeroCompactification {ℓ n : ℕ}
    {X : SchemeOverField k}
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))) :
    Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))) :=
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} (ZMod (ℓ ^ n)))).obj F

/-- The geometric fibre of a compactification after base change to `AlgebraicClosure k`. -/
abbrev geometricFibre {X : SchemeOverField k}
    (P : Compactification.Of (Spec (CommRingCat.of k)) X) : Scheme.{u} :=
  FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom

/-- The geometric fibre is the field-extension base change of the compactification. -/
theorem geometricFibre_eq {X : SchemeOverField k}
    (P : Compactification.Of (Spec (CommRingCat.of k)) X) :
    geometricFibre P =
      FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom := rfl

/-- Additive compactly supported étale cohomology `H^i_c` of the geometric fibre, as an
abelian group. -/
def etaleCohomologyCompactSupportAdd {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (geometricFibre P).smallEtaleTopology).IsRightAdjoint]
    [HasSheafify (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt (Sheaf (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u})]
    [(geometricFibre P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    AddCommGrpCat.{u} :=
  ((sheafCompose (geometricFibre P).smallEtaleTopology
        (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).obj
      ((zmodSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom) (ℓ ^ n)).obj
        (moduleExtensionByZeroCompactification P F))).H' i (globalEtale (geometricFibre P))

/-- Additive compactly supported cohomology is site cohomology of the forgotten geometric
pullback of the extension by zero. -/
theorem etaleCohomologyCompactSupportAdd_spec {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (geometricFibre P).smallEtaleTopology).IsRightAdjoint]
    [HasSheafify (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt (Sheaf (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u})]
    [(geometricFibre P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    etaleCohomologyCompactSupportAdd X P F i =
      ((sheafCompose (geometricFibre P).smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).obj
          ((zmodSheafPullback
              (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom) (ℓ ^ n)).obj
            (moduleExtensionByZeroCompactification P F))).H' i
        (globalEtale (geometricFibre P)) := rfl

/-- Compactly supported étale cohomology of a `ZMod (ℓ ^ n)`-sheaf is an `ℓ ^ n`-torsion
abelian group, hence a `ZMod (ℓ ^ n)`-module. -/
instance instModule_etaleCohomologyCompactSupportAdd {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (geometricFibre P).smallEtaleTopology).IsRightAdjoint]
    [HasSheafify (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt (Sheaf (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u})]
    [(geometricFibre P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    Module (ZMod (ℓ ^ n)) (etaleCohomologyCompactSupportAdd X P F i) :=
  AddCommGroup.zmodModule (fun _ ↦ sorry)

/-- Compactly supported étale cohomology `H^i_c(X ⊗_k AlgebraicClosure k, F)`, obtained by
extending `F` by zero along a compactification and pulling back to the geometric fibre. -/
def etaleCohomologyCompactSupport {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint]
    [HasWeakSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasExt
      (Sheaf
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
        AddCommGrpCat.{u})]
    [(FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    ModuleCat.{u} (ZMod (ℓ ^ n)) :=
  ModuleCat.of (ZMod (ℓ ^ n)) (etaleCohomologyCompactSupportAdd X P F i)

/-- Unfolding of compactly supported étale cohomology as module-valued site cohomology of
the geometric pullback of the extension by zero. -/
theorem etaleCohomologyCompactSupport_spec {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint]
    [HasWeakSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      AddCommGrpCat.{u}]
    [HasExt
      (Sheaf
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
        AddCommGrpCat.{u})]
    [(FieldExtension.baseChange k (AlgebraicClosure k)
        P.obj.right.hom).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    etaleCohomologyCompactSupport X P F i =
      ModuleCat.of (ZMod (ℓ ^ n)) (etaleCohomologyCompactSupportAdd X P F i) := rfl

/-- Compactly supported étale cohomology is independent of the chosen compactification. -/
theorem etaleCohomologyCompactSupport_independent {ℓ n : ℕ}
    (X : SchemeOverField k)
    (P Q : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [Etale (Compactification.Of.ι Q)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι Q)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre P).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre Q).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify (geometricFibre P).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify (geometricFibre Q).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u}]
    [HasSheafify (geometricFibre Q).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt (Sheaf (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u})]
    [HasExt (Sheaf (geometricFibre Q).smallEtaleTopology AddCommGrpCat.{u})]
    [(geometricFibre P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})]
    [(geometricFibre Q).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    Nonempty
      (etaleCohomologyCompactSupport X P F i ≅
        etaleCohomologyCompactSupport X Q F i) := sorry

/-- The Galois automorphism of a compactification after base change to `AlgebraicClosure k`. -/
def geometricGaloisMap {X : SchemeOverField k}
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (σ : Gal(AlgebraicClosure k/k)) :
    FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom ⟶
      FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom :=
  FieldExtension.Galois.map k (AlgebraicClosure k) P.obj.right.hom σ

/-- Pullback-pasting isomorphism identifying inverse image along geometric Galois action
with the original geometric restriction, using that the Galois automorphism lies over `k`. -/
def galoisPullbackPastingIso {ℓ n : ℕ} {X : SchemeOverField k}
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (σ : Gal(AlgebraicClosure k/k))
    (G : Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify
      (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
      (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [((smallEtalePullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback (geometricGaloisMap P σ)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        (FieldExtension.baseChange k (AlgebraicClosure k) P.obj.right.hom).smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint]
    [((smallEtalePullback
          (geometricGaloisMap P σ ≫
            FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)).sheafPushforwardContinuous
        (ModuleCat.{u} (ZMod (ℓ ^ n)))
        P.obj.right.left.smallEtaleTopology
        (FieldExtension.baseChange k (AlgebraicClosure k)
          P.obj.right.hom).smallEtaleTopology).IsRightAdjoint] :
    (zmodSheafPullback (geometricGaloisMap P σ) (ℓ ^ n)).obj
        ((zmodSheafPullback
            (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom) (ℓ ^ n)).obj G) ≅
      (zmodSheafPullback
          (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom) (ℓ ^ n)).obj G :=
  (zmodSheafPullback_comp
      (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom)
      (geometricGaloisMap P σ) (ℓ ^ n)).app G ≪≫
    (zmodSheafPullback_congr
      (FieldExtension.Galois.map_toSource k (AlgebraicClosure k) P.obj.right.hom σ)
      (ℓ ^ n)).app G

/-- Geometric Frobenius on compactly supported étale cohomology, as cohomology pullback along
the Galois automorphism of `frob_k⁻¹` followed by the pasting identification of coefficients. -/
def geometricFrobenius_cohomologyCompactSupport {ℓ n : ℕ} [Fintype k]
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre P).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify (geometricFibre P).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt (Sheaf (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u})]
    [(geometricFibre P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})] :
    etaleCohomologyCompactSupport X P F i ⟶ etaleCohomologyCompactSupport X P F i :=
  let σ := (FiniteField.arithmeticFrobenius k)⁻¹
  let G := moduleExtensionByZeroCompactification P F
  let Fmod :=
    (zmodSheafPullback
        (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom) (ℓ ^ n)).obj G
  let Fadd :=
    (sheafCompose (geometricFibre P).smallEtaleTopology
        (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).obj Fmod
  let α := galoisPullbackPastingIso P σ G
  let commute := zmodSheafPullback_compSheafComposeIso (geometricGaloisMap P σ) Fmod
  let pull := cohomologyPullback (geometricGaloisMap P σ) Fadd i
  let identify := Sheaf.cohomologyMap commute.inv i (globalEtale (geometricFibre P))
  let pasting :=
    Sheaf.cohomologyMap
      ((sheafCompose (geometricFibre P).smallEtaleTopology
          (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).map α.hom)
      i (globalEtale (geometricFibre P))
  ModuleCat.ofHom (AddMonoidHom.toZModLinearMap (ℓ ^ n)
    ((pull ≫ identify ≫ pasting).hom :
      etaleCohomologyCompactSupportAdd X P F i →+
        etaleCohomologyCompactSupportAdd X P F i))

/-- Evaluating geometric Frobenius on compactly supported cohomology recovers the Galois
action of `frob_k⁻¹`. -/
theorem geometricFrobenius_cohomologyCompactSupport_spec {ℓ n : ℕ} [Fintype k]
    (X : SchemeOverField k)
    (P : Compactification.Of (Spec (CommRingCat.of k)) X)
    (F : Sheaf X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n))))
    (i : ℕ)
    [Etale (Compactification.Of.ι P)]
    [∀ G : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} (ZMod (ℓ ^ n)),
      (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
    [HasWeakSheafify X.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre P).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasWeakSheafify (geometricFibre P).smallEtaleTopology (ModuleCat.{u} (ZMod (ℓ ^ n)))]
    [HasSheafify (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt (Sheaf (geometricFibre P).smallEtaleTopology AddCommGrpCat.{u})]
    [(geometricFibre P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})]
    (x : etaleCohomologyCompactSupport X P F i) :
    (geometricFrobenius_cohomologyCompactSupport X P F i).hom x =
      let σ := (FiniteField.arithmeticFrobenius k)⁻¹
      let G := moduleExtensionByZeroCompactification P F
      let Fmod :=
        (zmodSheafPullback
            (FieldExtension.toSource k (AlgebraicClosure k) P.obj.right.hom) (ℓ ^ n)).obj G
      let Fadd :=
        (sheafCompose (geometricFibre P).smallEtaleTopology
            (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).obj Fmod
      let α := galoisPullbackPastingIso P σ G
      let commute := zmodSheafPullback_compSheafComposeIso (geometricGaloisMap P σ) Fmod
      let pull := cohomologyPullback (geometricGaloisMap P σ) Fadd i
      let identify := Sheaf.cohomologyMap commute.inv i (globalEtale (geometricFibre P))
      let pasting :=
        Sheaf.cohomologyMap
          ((sheafCompose (geometricFibre P).smallEtaleTopology
              (forget₂ (ModuleCat.{u} (ZMod (ℓ ^ n))) AddCommGrpCat.{u})).map α.hom)
          i (globalEtale (geometricFibre P))
      (pull ≫ identify ≫ pasting).hom x := rfl

end AlgebraicGeometry.Scheme.Etale
