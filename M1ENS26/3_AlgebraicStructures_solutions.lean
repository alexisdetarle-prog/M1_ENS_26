import Mathlib

section Groups

variable {G C : Type*} [Group G] [CommGroup C]

example (g e : G) (h : g * e = g) : e = 1 := by
  calc e = 1 * e := by rw [one_mul]
      _ = g⁻¹ * g * e := by rw [← inv_mul_cancel]
      _ = g⁻¹ * (g * e) := by rw [mul_assoc]
      _ = g⁻¹ * g := by rw [h]
      _ = 1 := by rw [inv_mul_cancel]
  -- rw [← left_eq_mul, h]

example (N : Subgroup C) : CommGroup (C ⧸ N) := by
  constructor
  rintro a b
  obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective N a
  obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective N b
  rw [← ha', ← hb'/- , QuotientGroup.mk'_apply, QuotientGroup.mk'_apply-/]
  simp only [QuotientGroup.mk'_apply]
  apply CommGroup.mul_comm
  -- exact QuotientGroup.Quotient.commGroup N

lemma quotComm_lemma (N : Subgroup C) : CommGroup (C ⧸ N) := by sorry

def quotComm_def (N : Subgroup C) : CommGroup (C ⧸ N) := by sorry

lemma unit_surj (A B : Type*) [CommRing A] [CommRing B] {f : A →+* B} (a : Aˣ) : IsUnit (f a) := by
  rcases a with ⟨u, v, huv, hvu⟩
  rw [isUnit_iff_exists]
  refine ⟨f v, ?_, ?_⟩
  · simp [← map_mul, huv]
  · simp [← map_mul, hvu]

open Ideal in
-- **FAE** Use later
theorem idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 := by
  set Ia := J.map <| RingHom.fst .. with hIa
  set Ib := J.map <| RingHom.snd .. with hIb
  use ⟨Ia, Ib⟩
  ext x
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · constructor
    · apply Ideal.mem_map_of_mem
      exact hx
    · apply Ideal.mem_map_of_mem
      exact hx
  · rw [mem_prod, mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective),
        mem_map_iff_of_surjective _ (RingHomSurjective.is_surjective)] at hx
    obtain ⟨⟨y, hy_mem, hyx⟩, ⟨z, hz_mem, hzx⟩⟩ := hx
    have : ⟨x.1, 0⟩ + ⟨0, x.2⟩ = x := Prod.fst_add_snd x
    rw [← this, ← hyx, ← hzx]
    simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk_add_mk, add_zero, zero_add]
    replace hyx : ⟨y.1, y.2⟩ * ⟨1, 0⟩ = (⟨y.1, 0⟩ : A × B) := by
        calc ⟨y.1, y.2⟩ * ⟨1, 0⟩ = ⟨y.1 * 1, y.2 * 0⟩ := by rfl
                               _ = (⟨y.1, 0⟩ : A × B) := by rw [mul_one, mul_zero]
    replace hzx : ⟨z.1, z.2⟩ * ⟨0, 1⟩ = (⟨0, z.2⟩ : A × B) := by
        calc ⟨z.1, z.2⟩ * ⟨0, 1⟩ = ⟨z.1 * 0, z.2 * 1⟩ := by rfl
                                 _ = (⟨0, z.2⟩ : A × B) := by rw [mul_one, mul_zero]
    rw [← zero_add y.1, ← add_zero z.2, ← Prod.mk_add_mk 0 y.1 z.2 0, ← hzx, ← hyx, Prod.mk.eta,
        Prod.mk.eta]
    apply J.add_mem (J.mul_mem_right _ hz_mem) (J.mul_mem_right _ hy_mem)


open Ideal in
-- **FAE** Use later
theorem idealProd' (A B : Type*) [CommRing A] [CommRing B] (J : Ideal (A × B)) :
    ∃ P : Ideal A × Ideal B, J = Ideal.prod P.1 P.2 :=
  ⟨⟨J.map <| RingHom.fst .., J.map <| RingHom.snd ..⟩, J.ideal_prod_eq⟩

-- def idealProd (A B : Type*) [CommRing A] [CommRing B] (J : Ideal A × B) : (Ideal A) x (Ideal B) := by

-- @[to_additive]
-- instance [IsCyclic G] (N : Subgroup G) : N.Normal :=
--     @N.normal_of_comm _ IsCyclic.commGroup
--
-- @[to_additive]
-- theorem isCyclic_quotient [IsCyclic G] (N : Subgroup G) : IsCyclic (G ⧸ N) :=
--     isCyclic_of_surjective _ <| QuotientGroup.mk'_surjective _


end Groups
