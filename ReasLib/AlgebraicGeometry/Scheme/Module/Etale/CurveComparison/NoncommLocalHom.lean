module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.LinearSheafHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Etale.CurveComparison.ModuleRestrictionIso

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
noncomputable section
universe u

namespace NoncommLocalHom
variable {A R : Type (u + 1)} [CommRing A] [Ring R]
variable (h : A →+* R) (hc : ∀ (a : A) (r : R), h a * r = r * h a)

/-- Restriction along the specified coefficient map, on the original carriers. -/
abbrev modules := ModuleCat.restrictScalars h

/-- The same coefficient ring maps centrally to the opposite ring. -/
def opScalarHom : A →+* Rᵐᵒᵖ where
  toFun a := MulOpposite.op (h a)
  map_zero' := by simp
  map_one' := by simp
  map_add' := by intros; simp
  map_mul' := by
    intro a b
    apply MulOpposite.unop_injective
    change h (a * b) = h b * h a
    rw [map_mul, hc]

/-- Centrality is preserved when passing to the opposite ring without changing A. -/
theorem opScalarHom_central (a : A) (r : Rᵐᵒᵖ) :
    opScalarHom h hc a * r = r * opScalarHom h hc a := by
  apply MulOpposite.unop_injective
  exact (hc a r.unop).symm

/-- Left multiplication by r is A-linear after the actual scalar restriction. -/
def scalarModuleEnd (M : ModuleCat.{u + 1} R) (r : R) :
    (modules h).obj M ⟶ (modules h).obj M :=
  -- Local instance justification (defeq pin): this is the A-action used by ModuleCat.restrictScalars h on the same M.
  letI := Module.compHom M h
  ModuleCat.ofHom
    { toFun := fun m ↦ r • (m : M)
      map_add' := by intros; exact smul_add _ _ _
      map_smul' := by
        intro a m
        change r • (h a • m) = h a • (r • m)
        rw [smul_smul, smul_smul, hc] }

/-- The module-level precomposition used on every chart of local Hom. -/
def linearPrecomp (M : ModuleCat.{u + 1} R) (N : ModuleCat.{u + 1} A)
    (r : R) (f : (modules h).obj M ⟶ N) : (modules h).obj M ⟶ N :=
  scalarModuleEnd h hc M r ≫ f

variable (Y : Scheme.{u})
variable [Y.smallEtaleTopology.HasSheafCompose (modules h)]

/-- Scalar restriction of sheaves, retaining their sections and restriction functions. -/
abbrev sheaves := sheafCompose Y.smallEtaleTopology (modules h)

variable (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
variable (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))

/-- The genuine A-linear internal Hom into an arbitrary A-module sheaf J. -/
abbrev underlying := ActualLinearSheafHom.obj Y A ((sheaves h Y).obj F) J

/-- Multiplication by r on F, viewed only as an A-linear sheaf map. -/
def scalarEnd (r : R) : (sheaves h Y).obj F ⟶ (sheaves h Y).obj F :=
  ObjectProperty.homMk
    { app := fun U ↦ scalarModuleEnd h hc (F.obj.obj U) r
      naturality := sorry }

/-- Actual local natural transformations on the slice site, with no abstract Hom choice. -/
def Carrier (hc : ∀ (a : A) (r : R), h a * r = r * h a) (U : Y.Etaleᵒᵖ) :=
  (underlying h Y F J).obj.obj U

instance carrier_addCommGroup (U : Y.Etaleᵒᵖ) : AddCommGroup (Carrier h Y F J hc U) :=
  inferInstanceAs (AddCommGroup ((underlying h Y F J).obj.obj U))

instance carrier_coefficientModule (U : Y.Etaleᵒᵖ) : Module A (Carrier h Y F J hc U) :=
  inferInstanceAs (Module A ((underlying h Y F J).obj.obj U))

/-- Opposite scalars act by source precomposition; the target has only its A-action. -/
def sectionAction (U : Y.Etaleᵒᵖ) : Rᵐᵒᵖ →+* Module.End A (Carrier h Y F J hc U) where
  toFun r :=
    { toFun := fun α ↦ Functor.whiskerLeft (Over.forget U.unop).op
        (scalarEnd h hc Y F r.unop).hom ≫ α
      map_add' := sorry
      map_smul' := sorry }
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

/-- Right R-modules are left R-opposite modules, using the specified precomposition. -/
instance carrier_rightModule (U : Y.Etaleᵒᵖ) : Module Rᵐᵒᵖ (Carrier h Y F J hc U) :=
  Module.compHom (Carrier h Y F J hc U) (sectionAction h hc Y F J U)

/-- The right-R internal-Hom presheaf has the original local-Hom restriction maps. -/
def presheaf : Y.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Rᵐᵒᵖ where
  obj U := ModuleCat.of Rᵐᵒᵖ (Carrier h Y F J hc U)
  map f := ModuleCat.ofHom
    { toFun := fun α ↦ ((underlying h Y F J).obj.map f).hom α
      map_add' := by intros; exact map_add _ _ _
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The right action changes neither the local-Hom sections nor their gluing. -/
theorem isSheaf : Presheaf.IsSheaf Y.smallEtaleTopology (presheaf h hc Y F J) := sorry

/-- Actual right-R local Hom into arbitrary J. No commutativity or finiteness of R is used. -/
def obj : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ) :=
  ⟨presheaf h hc Y F J, isSheaf h hc Y F J⟩

/-- Native A-scalars equal restriction of the right-R action along the same A→R-op. -/
theorem coefficient_smul (U : Y.Etaleᵒᵖ) (a : A) (α : Carrier h Y F J hc U) :
    opScalarHom h hc a • α = a • α := sorry

variable {F J}

/-- Contravariance in the left-R source and covariance in the A-linear target. -/
def map {F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)}
    {J' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (f : F' ⟶ F) (g : J ⟶ J') : obj h hc Y F J ⟶ obj h hc Y F' J' :=
  ObjectProperty.homMk
    { app := fun U ↦ ModuleCat.ofHom
        { toFun := fun α ↦
            Functor.whiskerLeft (Over.forget U.unop).op ((sheaves h Y).map f).hom ≫
              α ≫ Functor.whiskerLeft (Over.forget U.unop).op g.hom
          map_add' := sorry
          map_smul' := sorry }
      naturality := sorry }

/-- Source precomposition is a right-R sheaf morphism. -/
def precomp {F' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)} (f : F' ⟶ F) :
    obj h hc Y F J ⟶ obj h hc Y F' J := map h hc Y f (𝟙 J)

/-- Target postcomposition is a right-R sheaf morphism without any R-action on J. -/
def postcomp {J' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)} (g : J ⟶ J') :
    obj h hc Y F J ⟶ obj h hc Y F J' := map h hc Y (𝟙 F) g

/-- The genuine covariant local-Hom functor in its A-sheaf target. -/
def targetFunctor (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A) ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ) where
  obj J := obj h hc Y F J
  map f := postcomp h hc Y f
  map_id := sorry
  map_comp := sorry

/-- The same data as a contravariant functor in the source. -/
def sourceFunctor (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))ᵒᵖ ⥤
      Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Rᵐᵒᵖ) where
  obj F := obj h hc Y F.unop J
  map f := precomp h hc Y f.unop
  map_id := sorry
  map_comp := sorry

end NoncommLocalHom
