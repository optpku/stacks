/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Associativity
import StacksCheckRecall

/-!
# Associativity of derived étale lower shriek composition

Lemma 63.9.3: for separated finite-type morphisms of quasi-compact
quasi-separated schemes, the Lemma 63.9.2 composition identifications form a
commutative square `Rh_! ∘ Rg_! ∘ Rf_! ⇉ R(h ∘ g ∘ f)_!`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

universe u v

/- Lemma 63.9.3: Let `f : X ⟶ Y`, `g : Y ⟶ Z`, `h : Z ⟶ T` be separated
morphisms of finite type of quasi-compact and quasi-separated schemes. Then
the diagram of isomorphisms of Lemma 63.9.2 commutes. -/
@[stacks 0F7K] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.comp_assoc.{u, v} :
∀ {Y Z T : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z) (h : Z ⟶ T)
  [h6 : IsSeparated X.hom] [h7 : Hom.FiniteType X.hom]
  [h8 : IsSeparated g] [h9 : Hom.FiniteType g]
  [h10 : IsSeparated h] [h11 : Hom.FiniteType h] [h12 : CompactSpace X.left]
  [h13 : QuasiSeparatedSpace X.left] [h14 : CompactSpace Y] [h15 : QuasiSeparatedSpace Y] [h16 : CompactSpace Z]
  [h17 : QuasiSeparatedSpace Z] [h18 : CompactSpace T] [h19 : QuasiSeparatedSpace T]
  (A : AssocDiagram X g h) (Λ : Type u) [h22 : Ring Λ]
  [h23 : HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h24 : ∀ (U : X.left.Etale), HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [h25 : HasDerivedCategory.{v} (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [h26 : HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h27 : ∀ (U : Y.Etale), HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [h28 : HasDerivedCategory.{v} (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [h29 : HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h30 : ∀ (U : Z.Etale), HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [h31 : HasDerivedCategory.{v} (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
  [h32 :
    HasSheafify
      (CompDiagram.interior X g
          (AssocDiagram.compFG X g h A)).smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h33 :
    ∀
      (U :
        (CompDiagram.interior X g
            (AssocDiagram.compFG X g h A)).Etale),
      HasWeakSheafify
        ((CompDiagram.interior X g
                (AssocDiagram.compFG X g h
                  A)).smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h34 :
    HasDerivedCategory
      (Sheaf
        (CompDiagram.interior X g
            (AssocDiagram.compFG X g h A)).smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h35 :
    HasSheafify
      (AssocDiagram.compFG X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h36 :
    ∀
      (U :
        (AssocDiagram.compFG X g h
                    A).P_bar.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compFG X g h
                        A).P_bar.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h37 :
    HasDerivedCategory
      (Sheaf
        (AssocDiagram.compFG X g h
                    A).P_bar.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h38 :
    HasSheafify
      (AssocDiagram.compFG X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h39 :
    ∀
      (U :
        (AssocDiagram.compFG X g h A).P_g.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compFG X g h
                        A).P_g.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h40 :
    HasDerivedCategory
      (Sheaf
        (AssocDiagram.compFG X g h
                    A).P_g.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h41 :
    HasSheafify
      (CompDiagram.interior X g
          (AssocDiagram.compFG X g h A)).smallEtaleTopology
      AddCommGrpCat.{u}]
  [h42 :
    HasSheafify
      (AssocDiagram.compFG X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h43 :
    HasSheafify
      (AssocDiagram.compFG X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h44 : X.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h45 : Y.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h46 :
    (CompDiagram.interior X g
            (AssocDiagram.compFG X g h
              A)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h47 :
    (AssocDiagram.compFG X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h48 :
    (AssocDiagram.compFG X g h
                    A).P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h49 :
    (CompDiagram.interior X g
            (AssocDiagram.compFG X g h
              A)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h50 :
    (AssocDiagram.compFG X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h51 :
    (AssocDiagram.compFG X g h
                    A).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h52 :
    ∀ (F : Functor X.left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h53 :
    ∀
      (F :
        Functor
          (CompDiagram.interior X g
                (AssocDiagram.compFG X g h A)).Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.openImmersion X g
                (AssocDiagram.compFG X g h
                  A))).op.HasLeftKanExtension
        F]
  [h54 :
    ∀ (F : Functor X.left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h55 :
    ∀ (F : Functor Y.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (AssocDiagram.compFG X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h56 :
    ∀ (F : Functor X.left.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofInterior X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h57 :
    ∀
      (F :
        Functor
          (CompDiagram.interior X g
                (AssocDiagram.compFG X g h A)).Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.openImmersion X g
                (AssocDiagram.compFG X g h
                  A))).op.HasLeftKanExtension
        F]
  [h58 :
    ∀ (F : Functor X.left.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h59 :
    ∀ (F : Functor Y.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (AssocDiagram.compFG X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h60 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior X g
              (AssocDiagram.compFG X g h A)).ι).op]
  [h61 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.openImmersion X g
            (AssocDiagram.compFG X g h A))).op]
  [h62 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofComposite X g
              (AssocDiagram.compFG X g h A)).ι).op]
  [h63 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (AssocDiagram.compFG X g h A).P_g.ι).op]
  [h64 : HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h65 :
    ∀ (U : (Over.mk g).left.Etale),
      HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [h66 : HasSheafify T.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h67 : ∀ (U : T.Etale), HasWeakSheafify (T.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [h68 : HasDerivedCategory.{v} (Sheaf T.smallEtaleTopology (ModuleCat.{u} Λ))]
  [h69 :
    HasSheafify
      (CompDiagram.interior (Over.mk g) h
          (AssocDiagram.compHG X g h A)).smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h70 :
    ∀
      (U :
        (CompDiagram.interior (Over.mk g) h
            (AssocDiagram.compHG X g h A)).Etale),
      HasWeakSheafify
        ((CompDiagram.interior (Over.mk g) h
                (AssocDiagram.compHG X g h
                  A)).smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h71 :
    HasSheafify
      (AssocDiagram.compHG X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h72 :
    ∀
      (U :
        (AssocDiagram.compHG X g h
                    A).P_bar.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compHG X g h
                        A).P_bar.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h73 :
    HasDerivedCategory
      (Sheaf
        (AssocDiagram.compHG X g h
                    A).P_bar.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h74 :
    HasSheafify
      (AssocDiagram.compHG X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h75 :
    ∀
      (U :
        (AssocDiagram.compHG X g h A).P_g.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compHG X g h
                        A).P_g.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h76 :
    HasDerivedCategory
      (Sheaf
        (AssocDiagram.compHG X g h
                    A).P_g.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h77 :
    HasSheafify
      (CompDiagram.interior (Over.mk g) h
          (AssocDiagram.compHG X g h A)).smallEtaleTopology
      AddCommGrpCat.{u}]
  [h78 :
    HasSheafify
      (AssocDiagram.compHG X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h79 :
    HasSheafify
      (AssocDiagram.compHG X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h80 :
    (Over.mk g).left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h81 : Z.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h82 :
    (CompDiagram.interior (Over.mk g) h
            (AssocDiagram.compHG X g h
              A)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h83 :
    (AssocDiagram.compHG X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h84 :
    (AssocDiagram.compHG X g h
                    A).P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h85 :
    (CompDiagram.interior (Over.mk g) h
            (AssocDiagram.compHG X g h
              A)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h86 :
    (AssocDiagram.compHG X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h87 :
    (AssocDiagram.compHG X g h
                    A).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h88 :
    ∀ (F : Functor (Over.mk g).left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g)
                  h
                  (AssocDiagram.compHG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h89 :
    ∀
      (F :
        Functor
          (CompDiagram.interior (Over.mk g) h
                (AssocDiagram.compHG X g h A)).Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.openImmersion
                (Over.mk g) h
                (AssocDiagram.compHG X g h
                  A))).op.HasLeftKanExtension
        F]
  [h90 :
    ∀ (F : Functor (Over.mk g).left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g)
                  h
                  (AssocDiagram.compHG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h91 :
    ∀ (F : Functor Z.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (AssocDiagram.compHG X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h92 :
    ∀ (F : Functor (Over.mk g).left.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g)
                  h
                  (AssocDiagram.compHG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h93 :
    ∀
      (F :
        Functor
          (CompDiagram.interior (Over.mk g) h
                (AssocDiagram.compHG X g h A)).Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.openImmersion
                (Over.mk g) h
                (AssocDiagram.compHG X g h
                  A))).op.HasLeftKanExtension
        F]
  [h94 :
    ∀ (F : Functor (Over.mk g).left.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g)
                  h
                  (AssocDiagram.compHG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h95 :
    ∀ (F : Functor Z.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (AssocDiagram.compHG X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h96 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
              (AssocDiagram.compHG X g h A)).ι).op]
  [h97 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.openImmersion (Over.mk g) h
            (AssocDiagram.compHG X g h A))).op]
  [h98 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
              (AssocDiagram.compHG X g h A)).ι).op]
  [h99 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (AssocDiagram.compHG X g h A).P_g.ι).op]
  [h100 :
    HasSheafify
      (CompDiagram.interior X
          (CategoryStruct.comp g h)
          (AssocDiagram.compF X g h A)).smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h101 :
    ∀
      (U :
        (CompDiagram.interior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h A)).Etale),
      HasWeakSheafify
        ((CompDiagram.interior X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h
                  A)).smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h102 :
    HasDerivedCategory
      (Sheaf
        (CompDiagram.interior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h A)).smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h103 :
    HasSheafify
      (AssocDiagram.compF X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h104 :
    ∀
      (U :
        (AssocDiagram.compF X g h A).P_bar.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compF X g h
                        A).P_bar.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h105 :
    HasDerivedCategory
      (Sheaf
        (AssocDiagram.compF X g h
                    A).P_bar.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h106 :
    HasSheafify
      (AssocDiagram.compF X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h107 :
    ∀
      (U :
        (AssocDiagram.compF X g h A).P_g.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compF X g h
                        A).P_g.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h108 :
    HasSheafify
      (CompDiagram.interior X
          (CategoryStruct.comp g h)
          (AssocDiagram.compF X g h A)).smallEtaleTopology
      AddCommGrpCat.{u}]
  [h109 :
    HasSheafify
      (AssocDiagram.compF X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h110 :
    HasSheafify
      (AssocDiagram.compF X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h111 :
    (CompDiagram.interior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h
              A)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h112 :
    (AssocDiagram.compF X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h113 :
    (AssocDiagram.compF X g h
                    A).P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h114 :
    (CompDiagram.interior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h
              A)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h115 :
    (AssocDiagram.compF X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h116 :
    (AssocDiagram.compF X g h
                    A).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h117 :
    ∀ (F : Functor X.left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h118 :
    ∀
      (F :
        Functor
          (CompDiagram.interior X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h A)).Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.openImmersion X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h
                  A))).op.HasLeftKanExtension
        F]
  [h119 :
    ∀ (F : Functor X.left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofComposite X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h120 :
    ∀ (F : Functor Y.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (AssocDiagram.compF X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h121 :
    ∀ (F : Functor X.left.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofInterior X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h122 :
    ∀
      (F :
        Functor
          (CompDiagram.interior X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h A)).Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.openImmersion X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h
                  A))).op.HasLeftKanExtension
        F]
  [h123 :
    ∀ (F : Functor X.left.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofComposite X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h124 :
    ∀ (F : Functor Y.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (AssocDiagram.compF X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h125 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior X
              (CategoryStruct.comp g h)
              (AssocDiagram.compF X g h A)).ι).op]
  [h126 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.openImmersion X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h A))).op]
  [h127 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofComposite X
              (CategoryStruct.comp g h)
              (AssocDiagram.compF X g h A)).ι).op]
  [h128 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (AssocDiagram.compF X g h A).P_g.ι).op]
  [h129 :
    HasSheafify
      (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h130 :
    ∀ (U : (Over.mk (X.hom ≫ g)).left.Etale),
      HasWeakSheafify
        ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U)
        (ModuleCat.{u} Λ)]
  [h131 :
    HasSheafify
      (CompDiagram.interior
          (Over.mk (X.hom ≫ g)) h
          (AssocDiagram.compH X g h A)).smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h132 :
    ∀
      (U :
        (CompDiagram.interior
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h A)).Etale),
      HasWeakSheafify
        ((CompDiagram.interior
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h
                  A)).smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h133 :
    HasDerivedCategory
      (Sheaf
        (CompDiagram.interior
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h A)).smallEtaleTopology
        (ModuleCat.{u} Λ))]
  [h134 :
    HasSheafify
      (AssocDiagram.compH X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h135 :
    ∀
      (U :
        (AssocDiagram.compH X g h A).P_bar.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compH X g h
                        A).P_bar.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h136 :
    HasSheafify
      (AssocDiagram.compH X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h137 :
    ∀
      (U :
        (AssocDiagram.compH X g h A).P_g.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compH X g h
                        A).P_g.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h138 :
    HasSheafify
      (CompDiagram.interior
          (Over.mk (X.hom ≫ g)) h
          (AssocDiagram.compH X g h A)).smallEtaleTopology
      AddCommGrpCat.{u}]
  [h139 :
    HasSheafify
      (AssocDiagram.compH X g h
                  A).P_bar.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h140 :
    HasSheafify
      (AssocDiagram.compH X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h141 :
    (Over.mk (X.hom ≫ g)).left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h142 :
    (CompDiagram.interior
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h
              A)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h143 :
    (AssocDiagram.compH X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h144 :
    (AssocDiagram.compH X g h
                    A).P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h145 :
    (CompDiagram.interior
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h
              A)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h146 :
    (AssocDiagram.compH X g h
                    A).P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h147 :
    (AssocDiagram.compH X g h
                    A).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h148 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h149 :
    ∀
      (F :
        Functor
          (CompDiagram.interior
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h A)).Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.openImmersion
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h
                  A))).op.HasLeftKanExtension
        F]
  [h150 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h151 :
    ∀ (F : Functor Z.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (AssocDiagram.compH X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h152 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h153 :
    ∀
      (F :
        Functor
          (CompDiagram.interior
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h A)).Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.openImmersion
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h
                  A))).op.HasLeftKanExtension
        F]
  [h154 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h155 :
    ∀ (F : Functor Z.Etaleᵒᵖ AddCommGrpCat.{u}),
      (etaleRestriction
              (AssocDiagram.compH X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h156 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
              (Over.mk (X.hom ≫ g)) h
              (AssocDiagram.compH X g h A)).ι).op]
  [h157 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.openImmersion
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h A))).op]
  [h158 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
              (Over.mk (X.hom ≫ g)) h
              (AssocDiagram.compH X g h A)).ι).op]
  [h159 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (AssocDiagram.compH X g h A).P_g.ι).op]
  [h160 : HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h161 : ∀ (U : X.left.Etale), HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [h162 :
    HasSheafify
      (CompDiagram.ofInterior X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h
                  A)).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h163 :
    ∀
      (U :
        (CompDiagram.ofInterior X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).obj.right.left.Etale),
      HasWeakSheafify
        ((CompDiagram.ofInterior X
                      (CategoryStruct.comp g h)
                      (AssocDiagram.compF X g h
                        A)).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h164 :
    HasSheafify
      (CompDiagram.ofInterior X g
                (AssocDiagram.compFG X g h
                  A)).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h165 :
    ∀
      (U :
        (CompDiagram.ofInterior X g
                  (AssocDiagram.compFG X g h
                    A)).obj.right.left.Etale),
      HasWeakSheafify
        ((CompDiagram.ofInterior X g
                      (AssocDiagram.compFG X g h
                        A)).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h166 :
    ∀ (F : Functor X.left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h167 :
    ∀ (F : Functor X.left.Etaleᵒᵖ (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h168 : X.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h169 :
    (CompDiagram.ofInterior X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h170 :
    (CompDiagram.ofInterior X g
                  (AssocDiagram.compFG X g h
                    A)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h171 : HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
  [h172 :
    HasSheafify
      (CompDiagram.ofInterior X
                (CategoryStruct.comp g h)
                (AssocDiagram.compF X g h
                  A)).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h173 :
    HasSheafify
      (CompDiagram.ofInterior X g
                (AssocDiagram.compFG X g h
                  A)).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h174 :
    (CompDiagram.ofInterior X
                  (CategoryStruct.comp g h)
                  (AssocDiagram.compF X g h
                    A)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h175 :
    (CompDiagram.ofInterior X g
                  (AssocDiagram.compFG X g h
                    A)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h176 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior X
              (CategoryStruct.comp g h)
              (AssocDiagram.compF X g h A)).ι).op]
  [h177 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior X g
              (AssocDiagram.compFG X g h A)).ι).op]
  [h178 :
    (etaleExtensionByZero
        (CompDiagram.ofInterior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h A)).ι
        (ModuleCat.{u} Λ)).Additive]
  [h179 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ofInterior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h180 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ofInterior X
            (CategoryStruct.comp g h)
            (AssocDiagram.compF X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h181 :
    (etaleExtensionByZero
        (CompDiagram.ofInterior X g
            (AssocDiagram.compFG X g h A)).ι
        (ModuleCat.{u} Λ)).Additive]
  [h182 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ofInterior X g
            (AssocDiagram.compFG X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h183 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ofInterior X g
            (AssocDiagram.compFG X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h184 :
    HasSheafify
      (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [h185 :
    ∀ (U : (Over.mk (X.hom ≫ g)).left.Etale),
      HasWeakSheafify
        ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U)
        (ModuleCat.{u} Λ)]
  [h186 :
    HasSheafify
      (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h
                  A)).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h187 :
    ∀
      (U :
        (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).obj.right.left.Etale),
      HasWeakSheafify
        ((CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                      (Over.mk (X.hom ≫ g)) h
                      (AssocDiagram.compH X g h
                        A)).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h188 :
    HasSheafify
      (CompDiagram.ofComposite X g
                (AssocDiagram.compFG X g h
                  A)).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h189 :
    ∀
      (U :
        (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).obj.right.left.Etale),
      HasWeakSheafify
        ((CompDiagram.ofComposite X g
                      (AssocDiagram.compFG X g h
                        A)).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h190 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h191 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h192 :
    (Over.mk (X.hom ≫ g)).left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h193 :
    (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h194 :
    (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h195 :
    HasSheafify
      (Over.mk (X.hom ≫ g)).left.smallEtaleTopology AddCommGrpCat.{u}]
  [h196 :
    HasSheafify
      (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                (Over.mk (X.hom ≫ g)) h
                (AssocDiagram.compH X g h
                  A)).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h197 :
    HasSheafify
      (CompDiagram.ofComposite X g
                (AssocDiagram.compFG X g h
                  A)).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h198 :
    (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h199 :
    (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h200 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
                  (Over.mk (X.hom ≫ g)) h
                  (AssocDiagram.compH X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h201 :
    ∀
      (F :
        Functor (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofComposite X g
                  (AssocDiagram.compFG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h202 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
              (Over.mk (X.hom ≫ g)) h
              (AssocDiagram.compH X g h A)).ι).op]
  [h203 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofComposite X g
              (AssocDiagram.compFG X g h A)).ι).op]
  [h204 :
    (etaleExtensionByZero
        (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h A)).ι
        (ModuleCat.{u} Λ)).Additive]
  [h205 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h206 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ofInterior (h_f_separated := inferInstanceAs (IsSeparated (X.hom ≫ g)))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType (X.hom ≫ g)))
        (h_X_compact := inferInstanceAs (CompactSpace X.left))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace X.left))
            (Over.mk (X.hom ≫ g)) h
            (AssocDiagram.compH X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h207 :
    (etaleExtensionByZero
        (CompDiagram.ofComposite X g
            (AssocDiagram.compFG X g h A)).ι
        (ModuleCat.{u} Λ)).Additive]
  [h208 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ofComposite X g
            (AssocDiagram.compFG X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h209 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ofComposite X g
            (AssocDiagram.compFG X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h210 :
    HasSheafify (Over.mk (CategoryStruct.comp g h)).left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h211 :
    ∀ (U : (Over.mk (CategoryStruct.comp g h)).left.Etale),
      HasWeakSheafify
        ((Over.mk (CategoryStruct.comp g h)).left.smallEtaleTopology.over U)
        (ModuleCat.{u} Λ)]
  [h212 :
    HasSheafify
      (AssocDiagram.compF X g h
                  A).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h213 :
    ∀
      (U :
        (AssocDiagram.compF X g h A).P_g.obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.compF X g h
                        A).P_g.obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h214 :
    HasSheafify
      (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
                (AssocDiagram.compHG X g h
                  A)).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h215 :
    ∀
      (U :
        (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
                  (AssocDiagram.compHG X g h
                    A)).obj.right.left.Etale),
      HasWeakSheafify
        ((CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
                      (AssocDiagram.compHG X g h
                        A)).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h216 :
    ∀
      (F :
        Functor (Over.mk (CategoryStruct.comp g h)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (AssocDiagram.compF X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h217 :
    ∀
      (F :
        Functor (Over.mk (CategoryStruct.comp g h)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g)
                  h
                  (AssocDiagram.compHG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h218 :
    (Over.mk (CategoryStruct.comp g h)).left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h219 :
    (AssocDiagram.compF X g h
                    A).P_g.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h220 :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
                  (AssocDiagram.compHG X g h
                    A)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h221 :
    HasSheafify (Over.mk (CategoryStruct.comp g h)).left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h222 :
    HasSheafify
      (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
                (AssocDiagram.compHG X g h
                  A)).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h223 :
    (AssocDiagram.compF X g h
                    A).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h224 :
    (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
                  (AssocDiagram.compHG X g h
                    A)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h225 :
    ∀
      (F :
        Functor (Over.mk (CategoryStruct.comp g h)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (AssocDiagram.compF X g h
                    A).P_g.ι).op.HasLeftKanExtension
        F]
  [h226 :
    ∀
      (F :
        Functor (Over.mk (CategoryStruct.comp g h)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g)
                  h
                  (AssocDiagram.compHG X g h
                    A)).ι).op.HasLeftKanExtension
        F]
  [h227 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (AssocDiagram.compF X g h A).P_g.ι).op]
  [h228 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
              (AssocDiagram.compHG X g h A)).ι).op]
  [h229 :
    (etaleExtensionByZero
        (AssocDiagram.compF X g h A).P_g.ι
        (ModuleCat.{u} Λ)).Additive]
  [h230 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (AssocDiagram.compF X g h A).P_g.ι (ModuleCat.{u} Λ))]
  [h231 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (AssocDiagram.compF X g h A).P_g.ι (ModuleCat.{u} Λ))]
  [h232 :
    (etaleExtensionByZero
        (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
            (AssocDiagram.compHG X g h A)).ι
        (ModuleCat.{u} Λ)).Additive]
  [h233 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
            (AssocDiagram.compHG X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h234 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (CompDiagram.ofComposite (h_f_separated := inferInstanceAs (IsSeparated g))
        (h_f_finiteType := inferInstanceAs (Hom.FiniteType g))
        (h_X_compact := inferInstanceAs (CompactSpace Y))
        (h_X_quasiSeparated := inferInstanceAs (QuasiSeparatedSpace Y)) (Over.mk g) h
            (AssocDiagram.compHG X g h A)).ι
        (ModuleCat.{u} Λ))]
  [h235 :
    HasSheafify
      (Over.mk
            (CategoryStruct.comp (X.hom ≫ g) h)).left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h236 :
    ∀
      (U :
        (Over.mk
              (CategoryStruct.comp (X.hom ≫ g) h)).left.Etale),
      HasWeakSheafify
        ((Over.mk
                  (CategoryStruct.comp (X.hom ≫ g)
                    h)).left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h237 :
    HasSheafify
      (CanonicalAssociativity.endpointAB X g h
                A).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h238 :
    ∀
      (U :
        (CanonicalAssociativity.endpointAB X g h
                  A).obj.right.left.Etale),
      HasWeakSheafify
        ((CanonicalAssociativity.endpointAB X g h
                      A).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h239 :
    HasSheafify
      (AssocDiagram.finalBC X g h
                A).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ)]
  [h240 :
    ∀ (U : (AssocDiagram.finalBC X g h A).obj.right.left.Etale),
      HasWeakSheafify
        ((AssocDiagram.finalBC X g h
                      A).obj.right.left.smallEtaleTopology.over
          U)
        (ModuleCat.{u} Λ)]
  [h241 :
    ∀
      (F :
        Functor
          (Over.mk
                  (CategoryStruct.comp (X.hom ≫ g) h)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (CanonicalAssociativity.endpointAB X g h
                  A).ι).op.HasLeftKanExtension
        F]
  [h242 :
    ∀
      (F :
        Functor
          (Over.mk
                  (CategoryStruct.comp (X.hom ≫ g) h)).left.Etaleᵒᵖ
          (ModuleCat.{u} Λ)),
      (etaleRestriction
              (AssocDiagram.finalBC X g h
                  A).ι).op.HasLeftKanExtension
        F]
  [h243 :
    (Over.mk
              (CategoryStruct.comp (X.hom ≫ g)
                h)).left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h244 :
    (CanonicalAssociativity.endpointAB X g h
                  A).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h245 :
    (AssocDiagram.finalBC X g h
                  A).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h246 :
    HasSheafify
      (Over.mk
            (CategoryStruct.comp (X.hom ≫ g) h)).left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h247 :
    HasSheafify
      (CanonicalAssociativity.endpointAB X g h
                A).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h248 :
    HasSheafify
      (AssocDiagram.finalBC X g h
                A).obj.right.left.smallEtaleTopology
      AddCommGrpCat.{u}]
  [h249 :
    (CanonicalAssociativity.endpointAB X g h
                  A).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h250 :
    (AssocDiagram.finalBC X g h
                  A).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [h251 :
    ∀
      (F :
        Functor
          (Over.mk
                  (CategoryStruct.comp (X.hom ≫ g) h)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (CanonicalAssociativity.endpointAB X g h
                  A).ι).op.HasLeftKanExtension
        F]
  [h252 :
    ∀
      (F :
        Functor
          (Over.mk
                  (CategoryStruct.comp (X.hom ≫ g) h)).left.Etaleᵒᵖ
          AddCommGrpCat.{u}),
      (etaleRestriction
              (AssocDiagram.finalBC X g h
                  A).ι).op.HasLeftKanExtension
        F]
  [h253 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (CanonicalAssociativity.endpointAB X g h A).ι).op]
  [h254 :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
          (AssocDiagram.finalBC X g h A).ι).op]
  [h255 :
    (etaleExtensionByZero
        (CanonicalAssociativity.endpointAB X g h A).ι
        (ModuleCat.{u} Λ)).Additive]
  [h256 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (CanonicalAssociativity.endpointAB X g h A).ι
        (ModuleCat.{u} Λ))]
  [h257 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (CanonicalAssociativity.endpointAB X g h A).ι
        (ModuleCat.{u} Λ))]
  [h258 :
    (etaleExtensionByZero
        (AssocDiagram.finalBC X g h A).ι (ModuleCat.{u} Λ)).Additive]
  [h259 :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (AssocDiagram.finalBC X g h A).ι (ModuleCat.{u} Λ))]
  [h260 :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (AssocDiagram.finalBC X g h A).ι (ModuleCat.{u} Λ))],
  @CanonicalAssociativity.leftPath.{u, v}
    Y Z T X g h h6 h7 h8 h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 A Λ h22 h23
    h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35
    h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47
    h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59
    h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71
    h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83
    h84 h85 h86 h87 h88 h89 h90 h91 h92 h93 h94 h95
    h96 h97 h98 h99 h100 h101 h102 h103 h104 h105 h106 h107
    h108 h109 h110 h111 h112 h113 h114 h115 h116 h117 h118 h119
    h120 h121 h122 h123 h124 h125 h126 h127 h128 h129 h130 h131
    h132 h133 h134 h135 h136 h137 h138 h139 h140 h141 h142 h143
    h144 h145 h146 h147 h148 h149 h150 h151 h152 h153 h154 h155
    h156 h157 h158 h159 h160 h161 h162 h163 h164 h165 h166 h167
    h168 h169 h170 h171 h172 h173 h174 h175 h176 h177 h178 h179
    h180 h181 h182 h183 h184 h185 h186 h187 h188 h189 h190 h191
    h192 h193 h194 h195 h196 h197 h198 h199 h200 h201 h202 h203
    h204 h205 h206 h207 h208 h209 h210 h211 h212 h213 h214 h215
    h216 h217 h218 h219 h220 h221 h222 h223 h224 h225 h226 h227
    h228 h229 h230 h231 h232 h233 h234 h235 h236 h237 h238 h239
    h240 h241 h242 h243 h244 h245 h246 h247 h248 h249 h250 h251
    h252 h253 h254 h255 h256 h257 h258 h259 h260 =
  @CanonicalAssociativity.rightPath.{u, v}
    Y Z T X g h h6 h7 h8 h9 h10 h11
    h12 h13 h14 h15 h16 h17 h18 h19 A Λ h22 h23
    h24 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 h35
    h36 h37 h38 h39 h40 h41 h42 h43 h44 h45 h46 h47
    h48 h49 h50 h51 h52 h53 h54 h55 h56 h57 h58 h59
    h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71
    h72 h73 h74 h75 h76 h77 h78 h79 h80 h81 h82 h83
    h84 h85 h86 h87 h88 h89 h90 h91 h92 h93 h94 h95
    h96 h97 h98 h99 h100 h101 h102 h103 h104 h105 h106 h107
    h108 h109 h110 h111 h112 h113 h114 h115 h116 h117 h118 h119
    h120 h121 h122 h123 h124 h125 h126 h127 h128 h129 h130 h131
    h132 h133 h134 h135 h136 h137 h138 h139 h140 h141 h142 h143
    h144 h145 h146 h147 h148 h149 h150 h151 h152 h153 h154 h155
    h156 h157 h158 h159 h160 h161 h162 h163 h164 h165 h166 h167
    h168 h169 h170 h171 h172 h173 h174 h175 h176 h177 h178 h179
    h180 h181 h182 h183 h184 h185 h186 h187 h188 h189 h190 h191
    h192 h193 h194 h195 h196 h197 h198 h199 h200 h201 h202 h203
    h204 h205 h206 h207 h208 h209 h210 h211 h212 h213 h214 h215
    h216 h217 h218 h219 h220 h221 h222 h223 h224 h225 h226 h227
    h228 h229 h230 h231 h232 h233 h234 h235 h236 h237 h238 h239
    h240 h241 h242 h243 h244 h245 h246 h247 h248 h249 h250 h251
    h252 h253 h254 h255 h256 h257 h258 h259 h260)

end
