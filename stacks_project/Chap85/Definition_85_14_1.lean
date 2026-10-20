module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedModuleSystem
public import stacks_project.Chap85.Definition_85_14_1_System
import StacksCheckRecall

/-!
# Definition 85.14.1

In Situation 85.3.3, with a sheaf of rings `O` on `C_total`, a simplicial system
of the derived category of modules consists of objects `K_n` of `D(O_n)` and maps
`K_φ : Lf_φ^* K_m ⟶ K_n` in `D(O_n)` for `φ : m ⟶ n`, subject to
`K_{φ ∘ ψ} = K_φ ∘ Lf_φ^* K_ψ` after `Lf_{φ ∘ ψ}^* = Lf_φ^* ∘ Lf_ψ^*`.
The system is cartesian when every `K_φ` is an isomorphism. Morphisms are the
obvious stagewise natural maps.
-/

@[expose] public section

open CategoryTheory
open RingedSite (ToposHom)

noncomputable section

universe u v w

section

variable (X : SimplexCategory → RingedSite.{u, v, w})
variable [∀ n, (X n).siteTopology.HasSheafCompose (forget RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable (fHom : ∀ {m n : SimplexCategory}, (m ⟶ n) → ToposHom (X n) (X m))
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w} (fHom φ).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ToposHom.HasModulePullbackDerived (fHom φ)]
variable (comparisons : RingedSite.Simplicial.ModulePullbackFunctoriality X fHom)

/- Definition 85.14.1
A simplicial derived-module system consists of component objects and transitions
satisfying composition compatibility under the canonical derived-pullback comparison. -/
@[stacks 0D9N] #check
  (RingedSite.Simplicial.DerivedModuleSystem X fHom :
    RingedSite.Simplicial.ModulePullbackFunctoriality X fHom → Type (max u v (w + 1)))

#check (RingedSite.Simplicial.DerivedModuleSystem.IsCartesian :
  RingedSite.Simplicial.DerivedModuleSystem X fHom comparisons → Prop)

#check (RingedSite.Simplicial.DerivedModuleSystem.isCartesian_iff :
  ∀ K : RingedSite.Simplicial.DerivedModuleSystem X fHom comparisons,
    RingedSite.Simplicial.DerivedModuleSystem.IsCartesian K ↔
      ∀ {m n : SimplexCategory} (φ : m ⟶ n), IsIso (K.map φ))

#check (RingedSite.Simplicial.DerivedModuleSystem.Hom :
  RingedSite.Simplicial.DerivedModuleSystem X fHom comparisons →
    RingedSite.Simplicial.DerivedModuleSystem X fHom comparisons → Type (max u v (w + 1)))

#check (RingedSite.Simplicial.DerivedModuleSystem.Hom.naturality :
  ∀ {K L : RingedSite.Simplicial.DerivedModuleSystem X fHom comparisons}
    (α : RingedSite.Simplicial.DerivedModuleSystem.Hom K L)
    {m n : SimplexCategory} (φ : m ⟶ n),
    K.map φ ≫ α.app n =
      (fHom φ).modulePullbackDerived.map (α.app m) ≫ L.map φ)

end

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

#check (RingedSite.Simplicial.DerivedModuleSystemOnComponents C J O :
  Type (max u v (w + 1)))
