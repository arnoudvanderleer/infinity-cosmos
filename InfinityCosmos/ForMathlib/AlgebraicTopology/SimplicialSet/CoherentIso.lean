/-
Copyright (c) 2024 Johns Hopkins Category Theory Seminar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johns Hopkins Category Theory Seminar
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialSet.CompStruct
import InfinityCosmos.ForMathlib.AlgebraicTopology.SimplicialCategory.Basic

universe u v

open CategoryTheory

namespace CategoryTheory

/-- This is the free-living isomorphism as a category with objects called
`zero` and `one`. Perhaps these should have different names?-/
def WalkingIso : Type := Fin 2

def WalkingIso.zero : WalkingIso := (0 : Fin 2)
def WalkingIso.one : WalkingIso := (1 : Fin 2)

open WalkingIso

namespace WalkingIso

/-- The free isomorphism is the codiscrete category on two objects. Can we make this a special
case of the other definition?-/
instance : Category (WalkingIso) where
  Hom _ _ := Unit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩

section

variable {C : Type u} [Category.{v} C]

/-- Functors out of `WalkingIso` define isomorphisms in the target category.-/
def toIso  (F : WalkingIso ⥤ C) : (F.obj zero) ≅ (F.obj one) where
  hom := F.map PUnit.unit
  inv := F.map PUnit.unit
  hom_inv_id := by rw [← F.map_comp, ← F.map_id]; rfl
  inv_hom_id := by rw [← F.map_comp, ← F.map_id]; rfl

/-- From an isomorphism in a category, one can build a functor out of `WalkingIso` to
that category.-/
def fromIso {X Y : C} (e : X ≅ Y) : WalkingIso ⥤ C where
  obj := fun
    | (0 : Fin 2) => X
    | (1 : Fin 2) => Y
  map := @fun
    | (0 : Fin 2), (0 : Fin 2), _ => 𝟙 _
    | (0 : Fin 2), (1 : Fin 2),  _ => e.hom
    | (1 : Fin 2), (0 : Fin 2), _ => e.inv
    | (1 : Fin 2), (1 : Fin 2),  _ => 𝟙 _
  map_comp := by simp [WalkingIso, Quiver.Hom]

def equiv : (WalkingIso ⥤ C) ≃ Σ (X : C) (Y : C), (X ≅ Y) where
  toFun F := ⟨F.obj zero, F.obj one, toIso F⟩
  invFun p := fromIso p.2.2
  right_inv := fun ⟨X, Y, e⟩ ↦ rfl
  left_inv F := by
    apply Functor.hext
    · simp [WalkingIso]
      constructor <;> rfl
    · simp [WalkingIso]
      simp only [fromIso, toIso]
      constructor <;> constructor <;>
      ( intro ⟨⟩
        try rfl
        try (rw [← F.map_id]; rfl) )

end

def coev (i : WalkingIso) : Fin 1 ⥤ WalkingIso := ComposableArrows.mk₀ i

end WalkingIso

end CategoryTheory

namespace SSet

open Simplicial

def coherentIso : SSet := nerve WalkingIso

def coherentIso.hom : coherentIso _⦋1⦌ :=
  ComposableArrows.mk₁ (X₀ := WalkingIso.zero) (X₁ := WalkingIso.one) ⟨⟩

def coherentIso.inv : coherentIso _⦋1⦌ :=
  ComposableArrows.mk₁ (X₀ := WalkingIso.one) (X₁ := WalkingIso.zero) ⟨⟩

def coherentIso.hom_inv_id : coherentIso _⦋2⦌ :=
  ComposableArrows.mk₂ (X₀ := WalkingIso.zero) (X₁ := WalkingIso.one) (X₂ := WalkingIso.zero) ⟨⟩ ⟨⟩

def coherentIso.inv_hom_id : coherentIso _⦋2⦌ :=
  ComposableArrows.mk₂ (X₀ := WalkingIso.one) (X₁ := WalkingIso.zero) (X₂ := WalkingIso.one) ⟨⟩ ⟨⟩

def coherentIso_equiv_fun {n : ℕ} : coherentIso _⦋n⦌ ≃ (Fin (n + 1) → Fin 2) where
  toFun f := f.obj
  invFun f := .mk f (fun _ ↦ ⟨⟩) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
  left_inv _ := rfl
  right_inv _ := rfl

instance (n : ℕ) : DecidableEq (coherentIso _⦋n⦌) :=
  fun _ _ ↦ decidable_of_iff _ (Equiv.apply_eq_iff_eq coherentIso_equiv_fun)

instance (n : ℕ) : DecidableEq (Δ[n] ⟶ coherentIso) :=
  fun _ _ ↦ decidable_of_iff _ (yonedaEquiv.apply_eq_iff_eq)

namespace IsIso_of_coherentIso_morphism

  variable {X : SSet}
  variable {x₀ x₁ : X _⦋0⦌}
  variable {f : Edge x₀ x₁}
  variable (g : coherentIso ⟶ X)
  variable (h : f.edge = g.app _ coherentIso.hom)

  def vertex_eq_of_eq_simplex_faces
    {X : SSet}
    {hom : X _⦋1⦌}
    {inv : X _⦋1⦌}
    {h : X _⦋2⦌}
    (hf : X.δ (2 : Fin 3) h = hom)
    (hg : X.δ (0 : Fin 3) h = inv)
    : X.δ (0 : Fin 2) hom = X.δ (1 : Fin 2) inv
    := by
      rw [← hf, ← hg]
      show ((X.map _ ≫ X.map _) h = (X.map _ ≫ X.map _) h)
      rw [← X.map_comp, ← X.map_comp]
      rw [← op_comp, ← op_comp]
      congrm X.map (Quiver.Hom.op ?_) h
      decide

  def inv_edge : X _⦋1⦌
    := g.app _ coherentIso.inv

  def hom_inv_id_edge : X _⦋2⦌
    := g.app _ coherentIso.hom_inv_id

  def inv_hom_id_edge : X _⦋2⦌
    := g.app _ coherentIso.inv_hom_id

  def hom_inv_id_d₂
    : X.δ 2 (hom_inv_id_edge g) = f.edge
    := by
      show ((g.app _ ≫ X.map _) _ = _)
      rw [h]
      rw [← g.naturality]
      congrm g.app _ ?_
      decide

  def hom_inv_id_d₀
    : X.δ 0 (hom_inv_id_edge g) = inv_edge g
    := by
      show ((g.app _ ≫ X.map _) _ = _)
      rw [← g.naturality]
      rfl

  def hom_inv_id_d₁
    : X.δ 1 (hom_inv_id_edge g) = X.σ 0 x₀
    := by
      rw [← f.src_eq]
      rw [h]
      show ((g.app _ ≫ X.map _) _ = (g.app _ ≫ (X.map _ ≫ X.map _)) _)
      rw [← X.map_comp]
      rw [← g.naturality]
      rw [← g.naturality]
      congrm g.app _ ?_
      decide

  def inv_hom_id_d₂
    : X.δ 2 (inv_hom_id_edge g) = inv_edge g
    := by
      show ((g.app _ ≫ X.map _) _ = _)
      rw [← g.naturality]
      dsimp
      congrm g.app _ ?_
      decide

  def inv_hom_id_d₀
    : X.δ 0 (inv_hom_id_edge g) = f.edge
    := by
      show ((g.app _ ≫ X.map _) _ = _)
      rw [← g.naturality]
      exact h.symm

  def inv_hom_id_d₁
    : X.δ 1 (inv_hom_id_edge g) = X.σ 0 x₁
    := by
      rw [← f.tgt_eq]
      rw [h]
      show ((g.app _ ≫ X.map _) _ = (g.app _ ≫ (X.map _ ≫ X.map _)) _)
      rw [← X.map_comp]
      rw [← g.naturality]
      rw [← g.naturality]
      congrm g.app _ ?_
      decide

end IsIso_of_coherentIso_morphism

open IsIso_of_coherentIso_morphism

def IsIso_of_coherentIso_morphism
  {X : SSet}
  {x₀ x₁ : X _⦋0⦌}
  (f : Edge x₀ x₁)
  (g : {g : coherentIso ⟶ X // f.edge = g.app _ coherentIso.hom})
  : f.IsIso
  where
    inv := .mk
      (inv_edge g)
      ((vertex_eq_of_eq_simplex_faces (hom_inv_id_d₂ _ g.property) (hom_inv_id_d₀ _)).symm.trans f.tgt_eq)
      ((vertex_eq_of_eq_simplex_faces (inv_hom_id_d₂ _) (inv_hom_id_d₀ _ g.property)).trans f.src_eq)
    hom_inv_id := .mk
      (hom_inv_id_edge g)
      (hom_inv_id_d₂ _ g.property)
      (hom_inv_id_d₀ _)
      (hom_inv_id_d₁ _ g.property)
    inv_hom_id := .mk
      (inv_hom_id_edge g)
      (inv_hom_id_d₂ _)
      (inv_hom_id_d₀ _ g.property)
      (inv_hom_id_d₁ _ g.property)

end SSet
