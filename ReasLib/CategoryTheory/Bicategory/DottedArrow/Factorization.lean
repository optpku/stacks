module

public import ReasLib.CategoryTheory.Functor.MappingPath
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Factorization
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.Pasting

/-!
# Dotted-arrow factorization

This is the compatibility entry point for the mapping-path construction and its bicategorical
dotted-arrow application.  The reusable ordinary-category construction lives in
`CategoryTheory.Functor.MappingPath`; raw pseudopullback edge factorization lives in
`CategoryTheory.Bicategory.PseudoPullbackCone.factorRight`; the dotted-arrow calculus is split
between the right-factor and pasting leaves.
-/
