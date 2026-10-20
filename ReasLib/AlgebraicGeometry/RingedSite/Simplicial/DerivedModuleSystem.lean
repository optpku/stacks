module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.ModulePullback

/-!
# Simplicial systems in the derived category of modules

A system `(K_n, K_φ)` with `K_n` in `D(O_n)` and transition maps
`K_φ : Lf_φ^* K_m ⟶ K_n` in `D(O_n)`, compatible with composition of simplex operators under the
canonical derived-pullback comparisons.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite (ToposHom)
open CategoryTheory.SimplicialSites

noncomputable section

universe u v w

namespace RingedSite.Simplicial

/-- A simplicial system of the derived category of modules: objects `K_n` in `D(O_n)` and
maps `K_φ : Lf_φ^* K_m ⟶ K_n` compatible with composition under the canonical
derived-pullback comparison. -/
structure DerivedModuleSystem
    (X : SimplexCategory → RingedSite.{u, v, w})
    [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
    [UnivLE.{max u v, w}]
    (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
    [∀ {m n : SimplexCategory} (φ : m ⟶ n),
      ToposHom.HasModulePullbackDerived (fHom φ)]
    (functoriality : ModulePullbackFunctoriality X fHom) where
  /-- The object `K_n` of `D(O_n)`. -/
  obj : ∀ n : SimplexCategory, RingedSite.Hom.ModuleDerived.{w} (X n)
  /-- The transition `K_φ : Lf_φ^* K_m ⟶ K_n` in `D(O_n)`. -/
  map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (fHom φ).modulePullbackDerived.obj (obj m) ⟶ obj n
  /-- Transitions respect composition of simplex operators after derived-pullback comparison. -/
  map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
    (derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
        (functoriality.pullbackCompIso ψ φ)).app (obj l) ≫
      map (ψ ≫ φ) =
        (fHom φ).modulePullbackDerived.map (map ψ) ≫ map φ

namespace DerivedModuleSystem

variable {X : SimplexCategory → RingedSite.{u, v, w}}
variable [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable {fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m)}
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fHom φ)]
variable {functoriality : ModulePullbackFunctoriality X fHom}

/-- Build a derived-module system from objects, transitions, and composition compatibility. -/
def of (functoriality : ModulePullbackFunctoriality X fHom)
    (obj : ∀ n : SimplexCategory, RingedSite.Hom.ModuleDerived.{w} (X n))
    (map : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      (fHom φ).modulePullbackDerived.obj (obj m) ⟶ obj n)
    (map_comp : ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
      (derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
          (functoriality.pullbackCompIso ψ φ)).app (obj l) ≫
        map (ψ ≫ φ) =
          (fHom φ).modulePullbackDerived.map (map ψ) ≫ map φ) :
    DerivedModuleSystem X fHom functoriality where
  obj := obj
  map := map
  map_comp := map_comp

/-- The transitions of a derived-module system satisfy composition compatibility. -/
theorem spec (K : DerivedModuleSystem X fHom functoriality) :
    ∀ {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n),
        (derivedPullbackCompComparisonOf (fHom φ) (fHom ψ) (fHom (ψ ≫ φ))
            (functoriality.pullbackCompIso ψ φ)).app (K.obj l) ≫
          K.map (ψ ≫ φ) =
            (fHom φ).modulePullbackDerived.map (K.map ψ) ≫ K.map φ :=
  sorry

/-- A morphism of derived-module systems is a family of maps in each `D(O_n)` commuting with
the transitions `K_φ`. -/
structure Hom (K L : DerivedModuleSystem X fHom functoriality) where
  /-- The component morphism at stage `n`. -/
  app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n
  /-- Naturality with respect to simplex operators. -/
  naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    K.map φ ≫ app n =
      (fHom φ).modulePullbackDerived.map (app m) ≫ L.map φ

/-- Build a morphism of derived-module systems from stagewise maps satisfying naturality. -/
def homMk {K L : DerivedModuleSystem X fHom functoriality}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n =
        (fHom φ).modulePullbackDerived.map (app m) ≫ L.map φ) :
    Hom K L where
  app := app
  naturality := naturality

/-- The identity components commute with every transition. -/
theorem Hom.id_naturality (K : DerivedModuleSystem X fHom functoriality) :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ 𝟙 (K.obj n) =
        (fHom φ).modulePullbackDerived.map (𝟙 (K.obj m)) ≫ K.map φ := sorry

/-- The identity morphism has identity components in each degree. -/
def Hom.id (K : DerivedModuleSystem X fHom functoriality) : Hom K K :=
  homMk (fun n ↦ 𝟙 (K.obj n)) (Hom.id_naturality K)

/-- Composites of natural families commute with every transition. -/
theorem Hom.comp_naturality {K L M : DerivedModuleSystem X fHom functoriality}
    (α : Hom K L) (β : Hom L M) :
    ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ (α.app n ≫ β.app n) =
        (fHom φ).modulePullbackDerived.map (α.app m ≫ β.app m) ≫ M.map φ := sorry

/-- Composition of morphisms is composition of their components in each degree. -/
def Hom.comp {K L M : DerivedModuleSystem X fHom functoriality}
    (α : Hom K L) (β : Hom L M) : Hom K M :=
  homMk (fun n ↦ α.app n ≫ β.app n) (Hom.comp_naturality α β)

/-- Stagewise component of a morphism built by `homMk`. -/
theorem homMk_app {K L : DerivedModuleSystem X fHom functoriality}
    (app : ∀ n : SimplexCategory, K.obj n ⟶ L.obj n)
    (naturality : ∀ {m n : SimplexCategory} (φ : m ⟶ n),
      K.map φ ≫ app n =
        (fHom φ).modulePullbackDerived.map (app m) ≫ L.map φ)
    (n : SimplexCategory) :
    (homMk app naturality).app n = app n :=
  sorry

/-- A derived-module system is cartesian when every transition `K_φ` is an isomorphism. -/
def IsCartesian (K : DerivedModuleSystem X fHom functoriality) : Prop :=
  ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ)

/-- Cartesianness is equivalent to every transition map being an isomorphism. -/
theorem isCartesian_iff (K : DerivedModuleSystem X fHom functoriality) :
    IsCartesian K ↔ ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ) :=
  sorry

end DerivedModuleSystem

open CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable (O : Sheaf (topology C J) RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (ringedToposMap C J O φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (ringedToposMap C J O φ)]

/-- Derived-module systems on component ringed sites with their canonical pullback comparisons. -/
abbrev DerivedModuleSystemOnComponents :=
  DerivedModuleSystem (fun n ↦ componentRingedSite C J O n)
    (fun φ ↦ ringedToposMap C J O φ) (modulePullbackFunctoriality C J O)

end RingedSite.Simplicial
