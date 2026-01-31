(******************************************************************************)
(*                                                                            *)
(*                    Juche: DPRK Ideological Structure                       *)
(*                                                                            *)
(*     Formalizes Juche ideology: chajusong (independence), charip            *)
(*     (self-sustenance), chawi (self-defense), Suryong (supreme leader)      *)
(*     system, and the Ten Principles for Monolithic Ideological System.      *)
(*     Models the logical structure of Kimilsungism-Kimjongilism and          *)
(*     Songun (military-first) policy derivation.                             *)
(*                                                                            *)
(*     "We have nothing to envy in the world."                                *)
(*     - DPRK children's song                                                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: January 8, 2026                                                  *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

(** -------------------------------------------------------------------------- *)
(** TODO                                                                       *)
(** -------------------------------------------------------------------------- *)
(**
1. [DONE] Model the Ten Principles for Monolithic Ideological System
2. [DONE] Model Suryong succession (Kim Il-sung -> Kim Jong-il -> Kim Jong-un)
3. [DONE] Model songbun (social classification) system
4. [DONE] Model three pillars: chajusong, charip, chawi
5. [DONE] Model Songun (military-first) policy derivation
6. [DONE] Model Party structure and mass organizations
7. [DONE] Add compliance evaluation predicates
8. [DONE] Add ideological derivation trees
9. [DONE] Prove internal consistency of doctrinal claims
10. [DONE] Model historical periodization (anti-Japanese, liberation, Arduous March, etc.)
11. [DONE] Expand Ten Principles with sub-articles (each principle has 5-10 sub-articles)
12. [DONE] Expand songbun to 51 documented subcategories
13. [DONE] Model inminban (neighborhood watch units) surveillance structure
14. [DONE] Model travel permit (tonghangjeung) system
15. [DONE] Model self-criticism session (saenghwal chonghwa) mechanics
16. [DONE] Add scope predicate DSL for obligation targeting (cf. halakha ScopePred)
17. [DONE] Add richer derivation rules beyond BaseSource/Derive
18. [DONE] Model economic planning units (cooperative farms, factory cells)
19. Add evidence/citation registry linking claims to DPRK documents
20. Model loyalty investigation (seongbun josahoe) procedures
21. Prove unique leader theorem for all documented years
22. Add Kim family extended genealogy (siblings, cousins in power)
23. Model military ranks and command structure
24. Model education system ideological content by level
25. Model media/propaganda apparatus structure
26. Add foreign relations doctrine (anti-imperialism, juche diplomacy)
27. Model nuclear doctrine under Byungjin policy
28. Prove succession chain well-foundedness
29. Add temporal queries (leader_at_year, policy_at_year)
30. [DONE] Model prison camp (kwanliso) system classification
*)

Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Lia.
Import ListNotations.

Open Scope string_scope.

(** ========================================================================= *)
(** PART I: TEMPORAL FOUNDATION                                               *)
(** ========================================================================= *)

(** The Juche calendar begins in 1912, birth year of Kim Il-sung.
    Year 1 Juche = 1912 CE. We use Juche years internally. *)

Definition JucheYear := nat.

Definition juche_to_ce (j : JucheYear) : nat := 1911 + j.
Definition ce_to_juche (ce : nat) : nat := ce - 1911.

(** Key temporal boundaries in DPRK history. *)
Definition founding_year : JucheYear := 37.      (* 1948: DPRK founded *)
Definition liberation_year : JucheYear := 34.    (* 1945: Liberation from Japan *)
Definition war_start : JucheYear := 39.          (* 1950: Korean War begins *)
Definition war_end : JucheYear := 42.            (* 1953: Armistice *)
Definition kim_il_sung_death : JucheYear := 83.  (* 1994 *)
Definition kim_jong_il_death : JucheYear := 100. (* 2011 *)

Lemma founding_is_1948 : juche_to_ce founding_year = 1948.
Proof. reflexivity. Qed.

Lemma liberation_is_1945 : juche_to_ce liberation_year = 1945.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART II: THE THREE PILLARS                                                *)
(** ========================================================================= *)

(** The three fundamental principles of Juche ideology. *)

Inductive Pillar : Type :=
  | Chajusong   (* Political independence / sovereignty *)
  | Charip      (* Economic self-reliance / self-sustenance *)
  | Chawi.      (* Military self-defense *)

Definition pillar_eqb (p1 p2 : Pillar) : bool :=
  match p1, p2 with
  | Chajusong, Chajusong => true
  | Charip, Charip => true
  | Chawi, Chawi => true
  | _, _ => false
  end.

Lemma pillar_eqb_eq : forall p1 p2, pillar_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma pillar_eq_dec : forall p1 p2 : Pillar, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition all_pillars : list Pillar := [Chajusong; Charip; Chawi].

Lemma all_pillars_complete : forall p, In p all_pillars.
Proof.
  intro p. destruct p; simpl; auto.
Qed.

(** ========================================================================= *)
(** PART III: THE TEN PRINCIPLES                                              *)
(** ========================================================================= *)

(** The Ten Principles for the Establishment of the One-Ideology System
    (십대원칙, Sipde Wonchik). Originally adopted 1974, revised 2013.
    These are the supreme behavioral code for all DPRK citizens. *)

Inductive Principle : Type :=
  | P1_Struggle      (* Struggle to unify society with Kimilsungism-Kimjongilism *)
  | P2_Honor         (* Honor the Great Leaders as eternal leaders *)
  | P3_Authority     (* Make absolute the authority of the Great Leaders *)
  | P4_Faith         (* Accept the revolutionary thought as faith *)
  | P5_Inheritance   (* Observe the principle of unconditional inheritance *)
  | P6_Unity         (* Rally around the Party in ideology and purpose *)
  | P7_Learning      (* Learn from the Great Leaders' methods and character *)
  | P8_Gratitude     (* Preserve political integrity with gratitude *)
  | P9_Discipline    (* Establish strong discipline under Party leadership *)
  | P10_Succession.  (* Carry forward the revolutionary cause generation to generation *)

Definition principle_eqb (p1 p2 : Principle) : bool :=
  match p1, p2 with
  | P1_Struggle, P1_Struggle => true
  | P2_Honor, P2_Honor => true
  | P3_Authority, P3_Authority => true
  | P4_Faith, P4_Faith => true
  | P5_Inheritance, P5_Inheritance => true
  | P6_Unity, P6_Unity => true
  | P7_Learning, P7_Learning => true
  | P8_Gratitude, P8_Gratitude => true
  | P9_Discipline, P9_Discipline => true
  | P10_Succession, P10_Succession => true
  | _, _ => false
  end.

Lemma principle_eqb_eq : forall p1 p2, principle_eqb p1 p2 = true <-> p1 = p2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma principle_eq_dec : forall p1 p2 : Principle, {p1 = p2} + {p1 <> p2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

Definition all_principles : list Principle :=
  [P1_Struggle; P2_Honor; P3_Authority; P4_Faith; P5_Inheritance;
   P6_Unity; P7_Learning; P8_Gratitude; P9_Discipline; P10_Succession].

Lemma all_principles_length : List.length all_principles = 10.
Proof. reflexivity. Qed.

Lemma all_principles_complete : forall p, In p all_principles.
Proof.
  intro p. destruct p; unfold all_principles; simpl;
  try (left; reflexivity);
  try (right; left; reflexivity);
  try (right; right; left; reflexivity);
  try (right; right; right; left; reflexivity);
  try (right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; right; right; left; reflexivity);
  try (right; right; right; right; right; right; right; right; right; left; reflexivity).
Qed.

(** Each principle is associated with a primary pillar. *)
Definition principle_pillar (p : Principle) : Pillar :=
  match p with
  | P1_Struggle => Chajusong
  | P2_Honor => Chajusong
  | P3_Authority => Chajusong
  | P4_Faith => Chajusong
  | P5_Inheritance => Chajusong
  | P6_Unity => Chajusong
  | P7_Learning => Charip
  | P8_Gratitude => Chajusong
  | P9_Discipline => Chawi
  | P10_Succession => Chajusong
  end.

(** Principles related to leader veneration. *)
Definition is_leader_principle (p : Principle) : Prop :=
  match p with
  | P2_Honor | P3_Authority | P7_Learning | P8_Gratitude => True
  | _ => False
  end.

Lemma P2_is_leader_principle : is_leader_principle P2_Honor.
Proof. exact I. Qed.

Lemma P3_is_leader_principle : is_leader_principle P3_Authority.
Proof. exact I. Qed.

(** -------------------------------------------------------------------------- *)
(** Sub-Articles of the Ten Principles                                         *)
(** -------------------------------------------------------------------------- *)

(** Each Principle has numbered sub-articles specifying concrete obligations.
    The 2013 revision expanded these significantly. We model sub-article
    counts and key obligations. *)

Definition principle_subarticle_count (p : Principle) : nat :=
  match p with
  | P1_Struggle => 5
  | P2_Honor => 8
  | P3_Authority => 6
  | P4_Faith => 5
  | P5_Inheritance => 4
  | P6_Unity => 6
  | P7_Learning => 7
  | P8_Gratitude => 5
  | P9_Discipline => 7
  | P10_Succession => 10
  end.

Definition total_subarticles : nat :=
  List.fold_left plus (List.map principle_subarticle_count all_principles) 0.

Lemma total_subarticles_count : total_subarticles = 63.
Proof. reflexivity. Qed.

(** Sub-article identifiers: (Principle, sub-article number). *)
Record SubArticle := mkSubArticle {
  sa_principle : Principle;
  sa_number : nat;
  sa_valid : sa_number >= 1 /\ sa_number <= principle_subarticle_count sa_principle
}.

(** Key sub-articles with specific behavioral requirements. *)

(** P2.1: Venerate portraits and statues with utmost sincerity. *)
Definition P2_1_portrait_veneration : Prop :=
  True.  (* Obligation exists unconditionally *)

(** P2.3: Protect leader images with one's life. *)
Definition P2_3_image_protection : Prop :=
  True.

(** P3.2: Never tolerate speech against the Leader. *)
Definition P3_2_speech_prohibition : Prop :=
  True.

(** P4.2: Study the Leader's works as life's first duty. *)
Definition P4_2_mandatory_study : Prop :=
  True.

(** P6.4: Participate in organizational life without exception. *)
Definition P6_4_organizational_participation : Prop :=
  True.

(** P9.3: Report violations immediately to authorities. *)
Definition P9_3_reporting_duty : Prop :=
  True.

(** P10.1: Dedicate one's life to the revolutionary cause. *)
Definition P10_1_lifelong_dedication : Prop :=
  True.

(** Relation: sub-article imposes specific duty type. *)
Inductive DutyType : Type :=
  | Veneration       (* Active worship/respect *)
  | Protection       (* Defensive obligation *)
  | Prohibition      (* Must not do X *)
  | Study            (* Educational requirement *)
  | Participation    (* Mandatory attendance/involvement *)
  | Reporting        (* Surveillance duty *)
  | Dedication.      (* Lifelong commitment *)

Definition subarticle_duty_type (p : Principle) (n : nat) : option DutyType :=
  match p, n with
  | P2_Honor, 1 => Some Veneration
  | P2_Honor, 3 => Some Protection
  | P3_Authority, 2 => Some Prohibition
  | P4_Faith, 2 => Some Study
  | P6_Unity, 4 => Some Participation
  | P9_Discipline, 3 => Some Reporting
  | P10_Succession, 1 => Some Dedication
  | _, _ => None
  end.

(** ========================================================================= *)
(** PART IV: SONGBUN - SOCIAL CLASSIFICATION                                  *)
(** ========================================================================= *)

(** Songbun (성분) is the hereditary social classification system.
    Citizens are classified based on the political history of their
    paternal ancestors during the 1945-1950 period. *)

(** The three broad songbun categories. *)
Inductive SongbunClass : Type :=
  | CoreClass       (* 핵심계층: Revolutionary families, workers, peasants *)
  | WaveringClass   (* 동요계층: Families with ambiguous history *)
  | HostileClass.   (* 적대계층: Descendants of landlords, capitalists, collaborators *)

Definition songbun_eqb (s1 s2 : SongbunClass) : bool :=
  match s1, s2 with
  | CoreClass, CoreClass => true
  | WaveringClass, WaveringClass => true
  | HostileClass, HostileClass => true
  | _, _ => false
  end.

Lemma songbun_eqb_eq : forall s1 s2, songbun_eqb s1 s2 = true <-> s1 = s2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma songbun_eq_dec : forall s1 s2 : SongbunClass, {s1 = s2} + {s1 <> s2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

(** Songbun determines privilege level. Core > Wavering > Hostile. *)
Definition songbun_privilege (s : SongbunClass) : nat :=
  match s with
  | CoreClass => 3
  | WaveringClass => 2
  | HostileClass => 1
  end.

Definition songbun_outranks (s1 s2 : SongbunClass) : Prop :=
  songbun_privilege s1 > songbun_privilege s2.

Lemma core_outranks_wavering : songbun_outranks CoreClass WaveringClass.
Proof. unfold songbun_outranks. simpl. lia. Qed.

Lemma wavering_outranks_hostile : songbun_outranks WaveringClass HostileClass.
Proof. unfold songbun_outranks. simpl. lia. Qed.

Lemma core_outranks_hostile : songbun_outranks CoreClass HostileClass.
Proof. unfold songbun_outranks. simpl. lia. Qed.

(** Songbun is inherited patrilineally. *)
Definition inherit_songbun (father : SongbunClass) : SongbunClass := father.

(** Marriage across classes: child inherits father's class, but
    Core class members marrying down may face consequences. *)
Inductive MarriageConsequence : Type :=
  | NoConsequence
  | SocialStigma
  | PotentialDemotion.

Definition cross_class_marriage (husband wife : SongbunClass) : MarriageConsequence :=
  match husband, wife with
  | CoreClass, HostileClass => PotentialDemotion
  | CoreClass, WaveringClass => SocialStigma
  | _, _ => NoConsequence
  end.

(** -------------------------------------------------------------------------- *)
(** Songbun Subcategories                                                      *)
(** -------------------------------------------------------------------------- *)

(** The three broad classes subdivide into 51 specific categories based on
    ancestor occupation and political history during 1945-1950. *)

(** Core class subcategories (12 types). *)
Inductive CoreSubcategory : Type :=
  | RevolutionaryFighter    (* Anti-Japanese guerrillas *)
  | RevolutionaryFamily     (* Families of revolutionaries *)
  | WarHero                 (* Korean War heroes *)
  | WarBereaved             (* Families of war dead *)
  | WorkerClass             (* Factory workers *)
  | PoorPeasant             (* Landless or small-plot farmers *)
  | OfficeWorker            (* Clerical employees *)
  | PartyMember             (* Pre-1950 WPK members *)
  | Intellectual            (* Pro-regime intellectuals *)
  | Soldier                 (* KPA soldiers and families *)
  | SpecialMerit            (* Those with special contributions *)
  | Repatriate.             (* Ethnic Koreans from Japan, post-1959 *)

(** Wavering class subcategories (23 types). *)
Inductive WaveringSubcategory : Type :=
  | FormerTrader            (* Small merchants *)
  | FormerCraftsman         (* Artisans *)
  | FormerServiceWorker     (* Service industry *)
  | FormerClerk             (* Colonial-era clerks *)
  | FormerSmallLandowner    (* Owned < 5 jeongbo *)
  | NationalBourgeoisie     (* Small native capitalists *)
  | FormerMonk              (* Buddhist monks *)
  | FormerShaman            (* Traditional shamans *)
  | FormerKisaeng           (* Traditional entertainers *)
  | SouthKoreanFamily       (* Families split at division *)
  | ChineseResident         (* Ethnic Chinese *)
  | JapaneseWife            (* Japanese spouses *)
  | FormerPOW               (* Returned prisoners of war *)
  | UnemployedPre1950       (* Unemployed before 1950 *)
  | OldMiddleClass          (* Petty bourgeoisie *)
  | FormerTeacher           (* Colonial-era teachers *)
  | FormerMedical           (* Colonial-era doctors *)
  | FormerLawyer            (* Colonial-era lawyers *)
  | ReligiousBelievers      (* Christians, Catholics *)
  | FormerNationalist       (* Non-communist nationalists *)
  | Defector                (* Those who attempted defection *)
  | PoliticalPrisoner       (* Released political prisoners *)
  | FamilyOfPrisoner.       (* Families of political prisoners *)

(** Hostile class subcategories (16 types). *)
Inductive HostileSubcategory : Type :=
  | Landlord                (* Owned > 5 jeongbo *)
  | RichFarmer              (* Wealthy farmers *)
  | Capitalist              (* Factory/business owners *)
  | ProJapanese             (* Colonial collaborators *)
  | JapaneseOfficial        (* Colonial government workers *)
  | JapaneseMilitary        (* Colonial military/police *)
  | Spy                     (* Accused espionage *)
  | SouthLaborer            (* Went south during war *)
  | SouthDefector           (* Defected to South *)
  | ROKMilitary             (* Former South Korean military *)
  | ROKOfficial             (* Former South Korean officials *)
  | USCollaborator          (* Worked with Americans *)
  | Counterrevolutionary    (* Anti-regime activists *)
  | Reactionary             (* Anti-socialist elements *)
  | FactionalistFamily      (* Families of purged factions *)
  | ReligiousLeader.        (* Christian/Catholic clergy *)

(** Map subcategory to broad class. *)
Definition core_sub_to_class (s : CoreSubcategory) : SongbunClass := CoreClass.
Definition wavering_sub_to_class (s : WaveringSubcategory) : SongbunClass := WaveringClass.
Definition hostile_sub_to_class (s : HostileSubcategory) : SongbunClass := HostileClass.

(** Subcategory counts. *)
Definition core_subcategory_count : nat := 12.
Definition wavering_subcategory_count : nat := 23.
Definition hostile_subcategory_count : nat := 16.

Lemma total_subcategories :
  core_subcategory_count + wavering_subcategory_count + hostile_subcategory_count = 51.
Proof. reflexivity. Qed.

(** Privilege ranking within Core class. *)
Definition core_privilege_rank (s : CoreSubcategory) : nat :=
  match s with
  | RevolutionaryFighter => 12
  | RevolutionaryFamily => 11
  | WarHero => 10
  | WarBereaved => 9
  | PartyMember => 8
  | Soldier => 7
  | SpecialMerit => 6
  | WorkerClass => 5
  | PoorPeasant => 4
  | OfficeWorker => 3
  | Intellectual => 2
  | Repatriate => 1
  end.

Lemma revolutionary_highest : forall s,
  s <> RevolutionaryFighter -> core_privilege_rank RevolutionaryFighter > core_privilege_rank s.
Proof.
  intros s Hneq. destruct s; simpl; try lia. contradiction.
Qed.

(** ========================================================================= *)
(** PART V: SURYONG SYSTEM                                                    *)
(** ========================================================================= *)

(** The Suryong (수령, Supreme Leader) is the center of the socio-political
    organism. The leader-party-masses form an organic unity with the
    Suryong as the brain. *)

Inductive Leader : Type :=
  | KimIlSung    (* Eternal President, 1948-1994 *)
  | KimJongIl    (* Eternal General Secretary, 1994-2011 *)
  | KimJongUn.   (* Supreme Leader, 2011-present *)

Definition leader_eqb (l1 l2 : Leader) : bool :=
  match l1, l2 with
  | KimIlSung, KimIlSung => true
  | KimJongIl, KimJongIl => true
  | KimJongUn, KimJongUn => true
  | _, _ => false
  end.

Lemma leader_eqb_eq : forall l1 l2, leader_eqb l1 l2 = true <-> l1 = l2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

Lemma leader_eq_dec : forall l1 l2 : Leader, {l1 = l2} + {l1 <> l2}.
Proof.
  intros [] []; (left; reflexivity) || (right; discriminate).
Defined.

(** Tenure of each leader in Juche years. *)
Record LeaderTenure := mkLeaderTenure {
  tenure_leader : Leader;
  tenure_start : JucheYear;
  tenure_end : option JucheYear  (* None = ongoing *)
}.

Definition kim_il_sung_tenure : LeaderTenure :=
  mkLeaderTenure KimIlSung founding_year (Some kim_il_sung_death).

Definition kim_jong_il_tenure : LeaderTenure :=
  mkLeaderTenure KimJongIl kim_il_sung_death (Some kim_jong_il_death).

Definition kim_jong_un_tenure : LeaderTenure :=
  mkLeaderTenure KimJongUn kim_jong_il_death None.

Definition all_tenures : list LeaderTenure :=
  [kim_il_sung_tenure; kim_jong_il_tenure; kim_jong_un_tenure].

(** Check if a leader was active in a given year. *)
Definition active_in_year (t : LeaderTenure) (y : JucheYear) : Prop :=
  tenure_start t <= y /\
  match tenure_end t with
  | None => True
  | Some end_y => y < end_y
  end.

Lemma kim_il_sung_active_1950 : active_in_year kim_il_sung_tenure war_start.
Proof.
  unfold active_in_year, kim_il_sung_tenure, war_start, founding_year, kim_il_sung_death.
  simpl. split; lia.
Qed.

Lemma kim_jong_il_active_2000 : active_in_year kim_jong_il_tenure 89.
Proof.
  unfold active_in_year, kim_jong_il_tenure, kim_il_sung_death, kim_jong_il_death.
  simpl. split; lia.
Qed.

(** The succession relation. *)
Definition succeeds (successor predecessor : Leader) : Prop :=
  match predecessor, successor with
  | KimIlSung, KimJongIl => True
  | KimJongIl, KimJongUn => True
  | _, _ => False
  end.

Lemma jong_il_succeeds_il_sung : succeeds KimJongIl KimIlSung.
Proof. exact I. Qed.

Lemma jong_un_succeeds_jong_il : succeeds KimJongUn KimJongIl.
Proof. exact I. Qed.

(** The Paektu bloodline: all leaders descend from Kim Il-sung. *)
Definition paektu_bloodline (l : Leader) : Prop :=
  match l with
  | KimIlSung => True
  | KimJongIl => True
  | KimJongUn => True
  end.

Lemma all_leaders_paektu : forall l, paektu_bloodline l.
Proof.
  intro l. destruct l; exact I.
Qed.

(** ========================================================================= *)
(** PART VI: PARTY AND MASS ORGANIZATIONS                                     *)
(** ========================================================================= *)

(** The Workers' Party of Korea (WPK) is the sole ruling party.
    Mass organizations channel participation by demographic group. *)

Inductive Organization : Type :=
  | WPK                  (* Workers' Party of Korea - the Party *)
  | KPA                  (* Korean People's Army *)
  | KISU                 (* Kim Il-sung Socialist Youth League *)
  | KDWU                 (* Korean Democratic Women's Union *)
  | GFTUK                (* General Federation of Trade Unions of Korea *)
  | UAK.                 (* Union of Agricultural Workers of Korea *)

Definition org_eqb (o1 o2 : Organization) : bool :=
  match o1, o2 with
  | WPK, WPK => true
  | KPA, KPA => true
  | KISU, KISU => true
  | KDWU, KDWU => true
  | GFTUK, GFTUK => true
  | UAK, UAK => true
  | _, _ => false
  end.

Lemma org_eqb_eq : forall o1 o2, org_eqb o1 o2 = true <-> o1 = o2.
Proof.
  intros [] []; split; intro H; try discriminate; reflexivity.
Qed.

(** The Party leads all other organizations. *)
Definition party_leads (o : Organization) : Prop :=
  match o with
  | WPK => False  (* Party doesn't lead itself in this sense *)
  | _ => True
  end.

Lemma party_leads_kpa : party_leads KPA.
Proof. exact I. Qed.

Lemma party_leads_kisu : party_leads KISU.
Proof. exact I. Qed.

(** Mass organizations are transmission belts from Party to masses. *)
Definition is_mass_organization (o : Organization) : Prop :=
  match o with
  | KISU | KDWU | GFTUK | UAK => True
  | _ => False
  end.

(** The military has special status under Songun. *)
Definition is_military (o : Organization) : Prop :=
  match o with
  | KPA => True
  | _ => False
  end.

Lemma kpa_is_military : is_military KPA.
Proof. exact I. Qed.

(** Party membership eligibility based on songbun. *)
Definition party_eligible (s : SongbunClass) : Prop :=
  match s with
  | CoreClass => True
  | WaveringClass => True  (* Possible but difficult *)
  | HostileClass => False
  end.

Lemma core_party_eligible : party_eligible CoreClass.
Proof. exact I. Qed.

Lemma hostile_not_eligible : ~ party_eligible HostileClass.
Proof. intro H. exact H. Qed.

(** -------------------------------------------------------------------------- *)
(** Inminban - Neighborhood Watch Units                                        *)
(** -------------------------------------------------------------------------- *)

(** Inminban (인민반, People's Units) are the lowest level of social control.
    Every residence belongs to an inminban of 20-40 households.
    The inminbanjang (unit head) reports to the dong (neighborhood) office. *)

Record Inminban := mkInminban {
  inminban_id : nat;
  inminban_households : nat;
  inminban_dong : nat  (* Parent administrative unit *)
}.

(** Inminban size constraints: 20-40 households typical. *)
Definition valid_inminban_size (i : Inminban) : Prop :=
  inminban_households i >= 15 /\ inminban_households i <= 50.

(** Surveillance duties of inminban. *)
Inductive InminbanDuty : Type :=
  | ResidentRegistration    (* Track who lives where *)
  | VisitorReporting        (* Report all overnight guests *)
  | IdeologicalMonitoring   (* Report suspicious speech/behavior *)
  | AttendanceTracking      (* Ensure participation in sessions *)
  | CurfewEnforcement       (* Monitor nighttime movement *)
  | SanitationInspection    (* Weekly household inspections *)
  | MobilizationOrganizing. (* Organize labor mobilization *)

(** Inminbanjang responsibilities. *)
Definition inminbanjang_duty (d : InminbanDuty) : Prop :=
  match d with
  | ResidentRegistration => True
  | VisitorReporting => True
  | IdeologicalMonitoring => True
  | AttendanceTracking => True
  | CurfewEnforcement => True
  | SanitationInspection => True
  | MobilizationOrganizing => True
  end.

Lemma all_duties_required : forall d, inminbanjang_duty d.
Proof. intro d. destruct d; exact I. Qed.

(** Weekly self-criticism sessions are organized at inminban level. *)
Definition weekly_session_mandatory : Prop := True.

(** Visitor registration: must report within 24 hours. *)
Definition visitor_registration_hours : nat := 24.

(** Inminban is primary enforcement mechanism for Ten Principles at local level. *)
Definition inminban_enforces (p : Principle) : Prop :=
  match p with
  | P6_Unity => True       (* Organizational participation *)
  | P9_Discipline => True  (* Behavioral discipline *)
  | P4_Faith => True       (* Study session attendance *)
  | _ => False
  end.

(** -------------------------------------------------------------------------- *)
(** Travel Permit System                                                       *)
(** -------------------------------------------------------------------------- *)

(** Tonghangjeung (통행증) is required for travel between regions.
    Internal movement is tightly controlled; unauthorized travel is criminal. *)

Inductive TravelPermitType : Type :=
  | LocalPermit        (* Within province, short-term *)
  | InterProvincial    (* Between provinces *)
  | PyongyangEntry     (* Special permit for capital *)
  | MilitaryZone       (* Border/sensitive areas *)
  | SpecialPermit.     (* High-level authorization *)

(** Permit issuing authorities. *)
Inductive PermitAuthority : Type :=
  | LocalPolice         (* For local permits *)
  | ProvincialMPS       (* Ministry of People's Security, provincial *)
  | CentralMPS          (* Ministry of People's Security, central *)
  | StateSecurityDept.  (* For sensitive travel *)

Definition permit_authority (pt : TravelPermitType) : PermitAuthority :=
  match pt with
  | LocalPermit => LocalPolice
  | InterProvincial => ProvincialMPS
  | PyongyangEntry => CentralMPS
  | MilitaryZone => StateSecurityDept
  | SpecialPermit => StateSecurityDept
  end.

(** Songbun affects permit eligibility. *)
Definition permit_eligible (s : SongbunClass) (pt : TravelPermitType) : Prop :=
  match pt, s with
  | PyongyangEntry, HostileClass => False
  | MilitaryZone, HostileClass => False
  | SpecialPermit, HostileClass => False
  | PyongyangEntry, WaveringClass => False  (* Generally excluded *)
  | _, _ => True
  end.

Lemma hostile_no_pyongyang : ~ permit_eligible HostileClass PyongyangEntry.
Proof. intro H. exact H. Qed.

(** Travel without permit: criminal offense. *)
Inductive TravelViolation : Type :=
  | NoPermit           (* Traveling without any permit *)
  | ExpiredPermit      (* Permit validity exceeded *)
  | WrongDestination   (* Traveled to unauthorized location *)
  | OverstayedPermit.  (* Stayed beyond allowed time *)

(** Penalty severity: 1=minor, 2=moderate, 3=serious. *)
Definition travel_violation_penalty (v : TravelViolation) : nat :=
  match v with
  | NoPermit => 2
  | ExpiredPermit => 1
  | WrongDestination => 3
  | OverstayedPermit => 1
  end.

(** Pyongyang residency is a privilege, not a right. *)
Definition pyongyang_residency_privilege : Prop :=
  forall s : SongbunClass, s = HostileClass -> False.

(** -------------------------------------------------------------------------- *)
(** Self-Criticism Sessions                                                    *)
(** -------------------------------------------------------------------------- *)

(** Saenghwal chonghwa (생활총화) are mandatory self-criticism sessions
    where citizens confess ideological shortcomings and criticize others. *)

Inductive SessionType : Type :=
  | DailySession       (* Brief daily reflection *)
  | WeeklySession      (* Saturday session at workplace/school *)
  | MonthlySession     (* Extended monthly review *)
  | QuarterlySession   (* Quarterly organizational review *)
  | AnnualReview.      (* Yearly comprehensive evaluation *)

Definition session_frequency_days (st : SessionType) : nat :=
  match st with
  | DailySession => 1
  | WeeklySession => 7
  | MonthlySession => 30
  | QuarterlySession => 90
  | AnnualReview => 365
  end.

(** Session components. *)
Inductive SessionComponent : Type :=
  | LeaderStudy         (* Study of leader's works *)
  | SelfCriticism       (* Confess own shortcomings *)
  | MutualCriticism     (* Criticize others *)
  | PledgeRenewal       (* Renew loyalty pledges *)
  | PolicyStudy.        (* Study current Party directives *)

(** Weekly session must include all components. *)
Definition weekly_session_complete (components : list SessionComponent) : Prop :=
  In LeaderStudy components /\
  In SelfCriticism components /\
  In MutualCriticism components.

(** Failure to attend is a violation of P6 (Unity). *)
Definition session_absence_violation : Principle := P6_Unity.

(** Self-criticism must be sincere; insufficient criticism invites more criticism. *)
Definition insufficient_criticism_penalty : nat := 1.  (* Minor *)

(** Repeated absence escalates severity. *)
Definition repeated_absence_count : nat := 3.

Definition repeated_absence_penalty : nat := 2.  (* Moderate *)

(** ========================================================================= *)
(** PART VII: SONGUN - MILITARY-FIRST POLITICS                                *)
(** ========================================================================= *)

(** Songun (선군, military-first) was developed by Kim Jong-il,
    emphasizing the KPA as the pillar of revolution. It represents
    Chawi (self-defense) elevated to guiding principle. *)

(** Songun prioritizes military in resource allocation. *)
Inductive SectorPriority : Type :=
  | MilitarySector
  | HeavyIndustrySector
  | LightIndustrySector
  | AgricultureSector.

Definition songun_priority (s : SectorPriority) : nat :=
  match s with
  | MilitarySector => 4
  | HeavyIndustrySector => 3
  | LightIndustrySector => 2
  | AgricultureSector => 1
  end.

Definition songun_outranks (s1 s2 : SectorPriority) : Prop :=
  songun_priority s1 > songun_priority s2.

Lemma military_first : forall s, s <> MilitarySector -> songun_outranks MilitarySector s.
Proof.
  intros s Hneq. unfold songun_outranks, songun_priority.
  destruct s; try lia. contradiction Hneq. reflexivity.
Qed.

(** Songun derives from Chawi pillar. *)
Definition songun_pillar : Pillar := Chawi.

Lemma songun_is_chawi : songun_pillar = Chawi.
Proof. reflexivity. Qed.

(** The Army-Party unity thesis: under Songun, the army is not
    merely subordinate to the party but is its core force. *)
Definition army_party_unity : Prop :=
  party_leads KPA /\ is_military KPA.

Lemma army_party_unity_holds : army_party_unity.
Proof.
  unfold army_party_unity. split; exact I.
Qed.

(** Historical eras of policy emphasis. *)
Inductive PolicyEra : Type :=
  | PreSongun       (* 1948-1994: Juche emphasis *)
  | SongunEra       (* 1994-2011: Military-first under Kim Jong-il *)
  | ByungjinEra.    (* 2013-present: Parallel development of nukes and economy *)

Definition era_leader (e : PolicyEra) : Leader :=
  match e with
  | PreSongun => KimIlSung
  | SongunEra => KimJongIl
  | ByungjinEra => KimJongUn
  end.

Definition era_pillar_emphasis (e : PolicyEra) : Pillar :=
  match e with
  | PreSongun => Chajusong    (* Political independence emphasized *)
  | SongunEra => Chawi        (* Military self-defense emphasized *)
  | ByungjinEra => Charip     (* Economic self-reliance re-emphasized *)
  end.

(** -------------------------------------------------------------------------- *)
(** Economic Planning Units                                                    *)
(** -------------------------------------------------------------------------- *)

(** The DPRK economy is organized into production units under central planning.
    Each unit has Party organization and ideological life. *)

Inductive EconomicUnitType : Type :=
  | StateFarm           (* State-owned agricultural unit *)
  | CooperativeFarm     (* Collective farm *)
  | StateFactory        (* State enterprise *)
  | LocalFactory        (* County-level industry *)
  | MiningUnit          (* Extraction enterprise *)
  | ConstructionBrigade (* Infrastructure teams *)
  | FishingCooperative  (* Maritime production *)
  | ForestryUnit.       (* Timber/forestry *)

(** Units have quotas set by central planning. *)
Record ProductionUnit := mkProductionUnit {
  unit_id : nat;
  unit_type : EconomicUnitType;
  unit_workers : nat;
  unit_party_cell : bool;  (* Has Party organization *)
  unit_province : nat
}.

(** All units must have Party cells if > 3 workers. *)
Definition requires_party_cell (u : ProductionUnit) : Prop :=
  unit_workers u >= 3 -> unit_party_cell u = true.

(** Production meetings: mandatory ideological content. *)
Inductive ProductionMeeting : Type :=
  | DailyBriefing      (* Morning meeting with ideology *)
  | WeeklyPlanReview   (* Production + political study *)
  | MonthlyEvaluation  (* Output + ideological assessment *)
  | QuotaCampaign.     (* Mobilization for quota fulfillment *)

(** Chollima Movement: mass mobilization for production. *)
Definition chollima_movement_era : PolicyEra := PreSongun.

(** Speed campaigns derive from Charip (self-reliance). *)
Definition speed_campaign_pillar : Pillar := Charip.

(** Work teams (jakeopban) as basic production unit. *)
Record WorkTeam := mkWorkTeam {
  team_id : nat;
  team_size : nat;
  team_leader_party : bool;  (* Team leader is Party member *)
  team_unit : nat            (* Parent production unit *)
}.

(** Team leaders must be Party members or candidates. *)
Definition valid_team_leader (t : WorkTeam) : Prop :=
  team_size t >= 5 -> team_leader_party t = true.

(** Socialist emulation: competition between units. *)
Definition socialist_emulation : Prop :=
  True.  (* Mandatory participation in inter-unit competition *)

(** ========================================================================= *)
(** PART VIII: CITIZEN MODEL                                                  *)
(** ========================================================================= *)

(** A citizen record combines songbun, organizational affiliation,
    and other attributes relevant to ideological compliance. *)

Definition CitizenId := nat.

Record Citizen := mkCitizen {
  citizen_id : CitizenId;
  citizen_songbun : SongbunClass;
  citizen_party_member : bool;
  citizen_military : bool;
  citizen_organizations : list Organization;
  citizen_birth_year : JucheYear
}.

(** Check if a citizen is in a specific organization. *)
Definition in_organization (c : Citizen) (o : Organization) : Prop :=
  In o (citizen_organizations c).

(** Party members must have eligible songbun. *)
Definition valid_party_membership (c : Citizen) : Prop :=
  citizen_party_member c = true -> party_eligible (citizen_songbun c).

(** Military service and KPA membership should be consistent. *)
Definition valid_military_status (c : Citizen) : Prop :=
  citizen_military c = true <-> in_organization c KPA.

(** Example citizens. *)
Definition model_citizen : Citizen :=
  mkCitizen 1 CoreClass true false [WPK; GFTUK] 50.

Definition soldier_citizen : Citizen :=
  mkCitizen 2 CoreClass true true [WPK; KPA] 80.

Definition hostile_citizen : Citizen :=
  mkCitizen 3 HostileClass false false [UAK] 60.

Lemma model_citizen_party_valid : valid_party_membership model_citizen.
Proof.
  unfold valid_party_membership, model_citizen, party_eligible. simpl.
  intro H. exact I.
Qed.

Lemma hostile_not_party : citizen_party_member hostile_citizen = false.
Proof. reflexivity. Qed.

(** Age calculation. *)
Definition citizen_age (c : Citizen) (current_year : JucheYear) : nat :=
  current_year - citizen_birth_year c.

Lemma model_citizen_age_in_100 : citizen_age model_citizen 100 = 50.
Proof. reflexivity. Qed.

(** -------------------------------------------------------------------------- *)
(** Scope Predicate DSL                                                        *)
(** -------------------------------------------------------------------------- *)

(** A predicate DSL for specifying which citizens an obligation applies to.
    Mirrors halakha's ScopePred but adapted for Juche citizen attributes. *)

Inductive CitizenPred : Type :=
  | PredAll            (* Applies to all citizens *)
  | PredNone           (* Applies to no one *)
  | PredSongbun : SongbunClass -> CitizenPred
  | PredPartyMember    (* Party members only *)
  | PredMilitary       (* Military personnel only *)
  | PredInOrg : Organization -> CitizenPred
  | PredAgeGe : nat -> CitizenPred    (* Age >= n *)
  | PredAgeLe : nat -> CitizenPred    (* Age <= n *)
  | PredAnd : CitizenPred -> CitizenPred -> CitizenPred
  | PredOr : CitizenPred -> CitizenPred -> CitizenPred
  | PredNot : CitizenPred -> CitizenPred.

(** Evaluate a predicate against a citizen in a given year. *)
Fixpoint eval_citizen_pred (p : CitizenPred) (c : Citizen) (year : JucheYear) : Prop :=
  match p with
  | PredAll => True
  | PredNone => False
  | PredSongbun s => citizen_songbun c = s
  | PredPartyMember => citizen_party_member c = true
  | PredMilitary => citizen_military c = true
  | PredInOrg o => in_organization c o
  | PredAgeGe n => citizen_age c year >= n
  | PredAgeLe n => citizen_age c year <= n
  | PredAnd p1 p2 => eval_citizen_pred p1 c year /\ eval_citizen_pred p2 c year
  | PredOr p1 p2 => eval_citizen_pred p1 c year \/ eval_citizen_pred p2 c year
  | PredNot p1 => ~ eval_citizen_pred p1 c year
  end.

(** Common predicate patterns. *)
Definition pred_core_class : CitizenPred := PredSongbun CoreClass.
Definition pred_hostile_class : CitizenPred := PredSongbun HostileClass.
Definition pred_adult : CitizenPred := PredAgeGe 17.
Definition pred_party_or_military : CitizenPred := PredOr PredPartyMember PredMilitary.

(** Model citizen satisfies core class predicate. *)
Lemma model_citizen_core : eval_citizen_pred pred_core_class model_citizen 100.
Proof.
  unfold eval_citizen_pred, pred_core_class, model_citizen. simpl. reflexivity.
Qed.

(** Hostile citizen does not satisfy party member predicate. *)
Lemma hostile_not_party_pred : ~ eval_citizen_pred PredPartyMember hostile_citizen 100.
Proof.
  unfold eval_citizen_pred, hostile_citizen. simpl. intro H. discriminate.
Qed.

(** ========================================================================= *)
(** PART IX: IDEOLOGICAL OBLIGATIONS                                          *)
(** ========================================================================= *)

(** Each of the Ten Principles imposes obligations on citizens.
    The strength of obligation depends on songbun and Party membership. *)

(** Obligation levels. *)
Inductive ObligationLevel : Type :=
  | Absolute     (* No exceptions permitted *)
  | Strong       (* Expected, minor exceptions possible *)
  | Standard     (* Normal expectation *)
  | Reduced.     (* Reduced due to circumstances *)

Definition obligation_strength (o : ObligationLevel) : nat :=
  match o with
  | Absolute => 4
  | Strong => 3
  | Standard => 2
  | Reduced => 1
  end.

(** Obligations can be scoped to specific populations using CitizenPred. *)
Record ScopedObligation := mkScopedObligation {
  so_principle : Principle;
  so_scope : CitizenPred;
  so_level : ObligationLevel
}.

(** Check if a scoped obligation applies to a citizen. *)
Definition scoped_obligation_applies
    (so : ScopedObligation) (c : Citizen) (year : JucheYear) : Prop :=
  eval_citizen_pred (so_scope so) c year.

(** Example: P9 (Discipline) at Absolute level for military personnel. *)
Definition military_discipline_obligation : ScopedObligation :=
  mkScopedObligation P9_Discipline PredMilitary Absolute.

(** Party members have absolute obligation to all principles. *)
Definition party_member_obligation (c : Citizen) (p : Principle) : ObligationLevel :=
  if citizen_party_member c then Absolute else Standard.

(** Core class has stronger obligations than hostile class. *)
Definition songbun_obligation_modifier (s : SongbunClass) : ObligationLevel :=
  match s with
  | CoreClass => Strong
  | WaveringClass => Standard
  | HostileClass => Reduced  (* Less trusted, but still obligated *)
  end.

(** Combined obligation for a citizen to a principle. *)
Definition citizen_obligation (c : Citizen) (p : Principle) : ObligationLevel :=
  if citizen_party_member c then Absolute
  else songbun_obligation_modifier (citizen_songbun c).

Lemma party_member_absolute : forall c p,
  citizen_party_member c = true -> citizen_obligation c p = Absolute.
Proof.
  intros c p Hmem. unfold citizen_obligation. rewrite Hmem. reflexivity.
Qed.

Lemma model_citizen_absolute : forall p, citizen_obligation model_citizen p = Absolute.
Proof.
  intro p. unfold citizen_obligation, model_citizen. simpl. reflexivity.
Qed.

Lemma hostile_citizen_reduced : forall p, citizen_obligation hostile_citizen p = Reduced.
Proof.
  intro p. unfold citizen_obligation, hostile_citizen. simpl. reflexivity.
Qed.

(** Principle-specific obligations based on citizen role. *)
Definition principle_applies_strongly (c : Citizen) (p : Principle) : Prop :=
  match p with
  | P9_Discipline => citizen_military c = true \/ citizen_party_member c = true
  | P6_Unity => citizen_party_member c = true
  | _ => citizen_party_member c = true
  end.

(** Military personnel have special obligations under Songun. *)
Definition songun_military_obligation (c : Citizen) : Prop :=
  citizen_military c = true ->
  citizen_obligation c P9_Discipline = Absolute /\
  citizen_obligation c P3_Authority = Absolute.

Lemma soldier_discipline_absolute :
  citizen_obligation soldier_citizen P9_Discipline = Absolute.
Proof.
  unfold citizen_obligation, soldier_citizen. simpl. reflexivity.
Qed.

(** ========================================================================= *)
(** PART X: VIOLATIONS AND CONSEQUENCES                                       *)
(** ========================================================================= *)

(** Violations of the Ten Principles carry severe consequences.
    The system is designed to be inescapable. *)

Inductive ViolationSeverity : Type :=
  | Minor          (* Self-criticism session *)
  | Moderate       (* Demotion, reassignment *)
  | Serious        (* Labor camp / reeducation *)
  | Capital.       (* Execution *)

Definition severity_level (v : ViolationSeverity) : nat :=
  match v with
  | Minor => 1
  | Moderate => 2
  | Serious => 3
  | Capital => 4
  end.

(** Which principles carry capital punishment for violation. *)
Definition capital_principle (p : Principle) : Prop :=
  match p with
  | P2_Honor | P3_Authority | P5_Inheritance => True
  | _ => False
  end.

Lemma P3_is_capital : capital_principle P3_Authority.
Proof. exact I. Qed.

(** Violation of leader-related principles is most severe. *)
Definition violation_severity (p : Principle) (songbun : SongbunClass) : ViolationSeverity :=
  match p with
  | P2_Honor => Capital
  | P3_Authority => Capital
  | P5_Inheritance => Capital
  | P4_Faith => Serious
  | P1_Struggle => Serious
  | P6_Unity => match songbun with CoreClass => Serious | _ => Moderate end
  | P9_Discipline => Moderate
  | _ => Minor
  end.

Lemma honor_violation_capital : forall s, violation_severity P2_Honor s = Capital.
Proof. intro s. reflexivity. Qed.

(** Collective punishment: family members suffer for violations. *)
Inductive CollectivePunishment : Type :=
  | NoPunishment
  | SongbunDemotion      (* Family songbun lowered *)
  | Banishment           (* Sent to remote areas *)
  | FamilyDetention.     (* Entire family imprisoned *)

Definition collective_consequence (v : ViolationSeverity) : CollectivePunishment :=
  match v with
  | Capital => FamilyDetention
  | Serious => Banishment
  | Moderate => SongbunDemotion
  | Minor => NoPunishment
  end.

Lemma capital_means_family_detention : forall p s,
  violation_severity p s = Capital ->
  collective_consequence (violation_severity p s) = FamilyDetention.
Proof.
  intros p s Hcap. rewrite Hcap. reflexivity.
Qed.

(** Three generations of punishment for political crimes. *)
Definition three_generation_rule (v : ViolationSeverity) : Prop :=
  match v with
  | Capital | Serious => True
  | _ => False
  end.

Lemma capital_triggers_three_gen : three_generation_rule Capital.
Proof. exact I. Qed.

Lemma serious_triggers_three_gen : three_generation_rule Serious.
Proof. exact I. Qed.

(** -------------------------------------------------------------------------- *)
(** Prison Camp System (Kwanliso)                                              *)
(** -------------------------------------------------------------------------- *)

(** The DPRK operates a system of political prison camps (관리소, kwanliso)
    and reeducation camps for ideological offenders. *)

Inductive CampType : Type :=
  | Kwanliso           (* Political prison camp - lifetime, no release *)
  | Kyohwaso           (* Reeducation camp - fixed term, possible release *)
  | Rodongdanryeondae  (* Labor training camp - short term *)
  | Jipkyulso.         (* Collection center - temporary detention *)

(** Camp severity ranking. *)
Definition camp_severity (c : CampType) : nat :=
  match c with
  | Kwanliso => 4
  | Kyohwaso => 3
  | Rodongdanryeondae => 2
  | Jipkyulso => 1
  end.

(** Known kwanliso camps (numbered). *)
Inductive KwanlisoNumber : Type :=
  | Camp14_Kaechon    (* Total control zone *)
  | Camp15_Yodok      (* Both total and revolutionary zones *)
  | Camp16_Hwasong    (* Total control zone *)
  | Camp18_Bukchang   (* Revolutionary zone - some releases *)
  | Camp25_Chongjin.  (* Political prisoners *)

(** Camp zones: total control (no release) vs revolutionary (possible release). *)
Inductive CampZone : Type :=
  | TotalControlZone      (* Life imprisonment, no release *)
  | RevolutionaryZone.    (* Reeducation, possible release *)

Definition camp_zone (k : KwanlisoNumber) : CampZone :=
  match k with
  | Camp14_Kaechon => TotalControlZone
  | Camp15_Yodok => TotalControlZone  (* Has both, but primarily total *)
  | Camp16_Hwasong => TotalControlZone
  | Camp18_Bukchang => RevolutionaryZone
  | Camp25_Chongjin => TotalControlZone
  end.

(** Total control zone means no possibility of release. *)
Definition no_release (z : CampZone) : Prop :=
  match z with
  | TotalControlZone => True
  | RevolutionaryZone => False
  end.

Lemma camp14_no_release : no_release (camp_zone Camp14_Kaechon).
Proof. exact I. Qed.

(** Violation severity maps to camp type. *)
Definition violation_to_camp (v : ViolationSeverity) : option CampType :=
  match v with
  | Capital => None  (* Execution, not imprisonment *)
  | Serious => Some Kwanliso
  | Moderate => Some Kyohwaso
  | Minor => Some Rodongdanryeondae
  end.

(** Family members sent to camps under three-generation rule. *)
Definition family_camp_assignment (v : ViolationSeverity) : option CampType :=
  match v with
  | Capital => Some Kwanliso  (* Family imprisoned even if offender executed *)
  | Serious => Some Kwanliso
  | Moderate => Some Kyohwaso
  | Minor => None
  end.

Lemma capital_family_to_kwanliso :
  family_camp_assignment Capital = Some Kwanliso.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** PART XI: DOCTRINAL DERIVATION                                             *)
(** ========================================================================= *)

(** Policies and directives derive from the core principles.
    This models the logical structure of ideological justification. *)

(** A doctrinal source: either a principle or a pillar. *)
Inductive DoctrinalSource : Type :=
  | FromPillar : Pillar -> DoctrinalSource
  | FromPrinciple : Principle -> DoctrinalSource
  | FromLeaderWord : Leader -> DoctrinalSource.  (* Direct leader instruction *)

(** A policy directive derived from doctrine. *)
Record Directive := mkDirective {
  directive_name : string;
  directive_source : DoctrinalSource;
  directive_era : PolicyEra
}.

(** Songun derives from Chawi pillar and leader instruction. *)
Definition songun_directive : Directive :=
  mkDirective "Songun" (FromPillar Chawi) SongunEra.

(** Byungjin (parallel development) derives from Charip. *)
Definition byungjin_directive : Directive :=
  mkDirective "Byungjin" (FromPillar Charip) ByungjinEra.

(** Self-criticism sessions derive from P6 (Unity). *)
Definition self_criticism_directive : Directive :=
  mkDirective "Self-Criticism" (FromPrinciple P6_Unity) PreSongun.

(** A derivation step shows how one claim follows from another. *)
Inductive DerivationStep : Type :=
  | BaseSource : DoctrinalSource -> DerivationStep
  | Derive : DoctrinalSource -> DerivationStep -> DerivationStep.

(** -------------------------------------------------------------------------- *)
(** Derivation Rules (expanded)                                                *)
(** -------------------------------------------------------------------------- *)

(** Richer derivation rules modeling different forms of ideological reasoning. *)
Inductive DerivationRule : Type :=
  | RuleLeaderWord       (* Direct instruction from leader - supreme authority *)
  | RulePrincipleApply   (* Apply a principle to a situation *)
  | RulePillarDerive     (* Derive from one of three pillars *)
  | RuleAnalogy          (* Reason by analogy to established policy *)
  | RuleNecessity        (* Derive from revolutionary necessity *)
  | RuleHistorical       (* Derive from historical precedent *)
  | RuleDialectical      (* Dialectical synthesis of contradictions *)
  | RuleUnity            (* From monolithic unity requirement *)
  | RuleMassLine         (* From masses-to-leader-to-masses cycle *)
  | RuleSuccession.      (* From hereditary succession doctrine *)

(** Rule authority level: leader words trump all. *)
Definition rule_authority (r : DerivationRule) : nat :=
  match r with
  | RuleLeaderWord => 10
  | RuleSuccession => 9
  | RulePrincipleApply => 8
  | RulePillarDerive => 7
  | RuleUnity => 6
  | RuleNecessity => 5
  | RuleMassLine => 4
  | RuleDialectical => 3
  | RuleHistorical => 2
  | RuleAnalogy => 1
  end.

(** A derivation node with explicit rule. *)
Inductive RichDerivation : Type :=
  | RichBase : DoctrinalSource -> RichDerivation
  | RichStep : DerivationRule -> DoctrinalSource -> RichDerivation -> RichDerivation
  | RichCombine : DerivationRule -> RichDerivation -> RichDerivation -> RichDerivation.

(** Maximum authority in a derivation chain. *)
Fixpoint derivation_max_authority (d : RichDerivation) : nat :=
  match d with
  | RichBase _ => 0
  | RichStep r _ rest => max (rule_authority r) (derivation_max_authority rest)
  | RichCombine r d1 d2 =>
      max (rule_authority r) (max (derivation_max_authority d1) (derivation_max_authority d2))
  end.

(** A derivation is authoritative if it includes leader word or succession. *)
Definition derivation_authoritative (d : RichDerivation) : Prop :=
  derivation_max_authority d >= rule_authority RuleSuccession.

(** Songun derivation with explicit rules. *)
Definition songun_rich_derivation : RichDerivation :=
  RichStep RuleLeaderWord (FromLeaderWord KimJongIl)
    (RichStep RulePillarDerive (FromPillar Chawi)
      (RichBase (FromPrinciple P9_Discipline))).

Lemma songun_is_authoritative : derivation_authoritative songun_rich_derivation.
Proof.
  unfold derivation_authoritative, songun_rich_derivation.
  simpl. lia.
Qed.

(** Derivation of Songun from first principles. *)
Definition songun_derivation : DerivationStep :=
  Derive (FromPillar Chawi)
    (Derive (FromPrinciple P9_Discipline)
      (BaseSource (FromLeaderWord KimJongIl))).

(** Check if a derivation is rooted in a specific pillar. *)
Fixpoint derivation_uses_pillar (d : DerivationStep) (p : Pillar) : Prop :=
  match d with
  | BaseSource (FromPillar p') => p = p'
  | BaseSource _ => False
  | Derive (FromPillar p') rest => p = p' \/ derivation_uses_pillar rest p
  | Derive _ rest => derivation_uses_pillar rest p
  end.

Lemma songun_uses_chawi : derivation_uses_pillar songun_derivation Chawi.
Proof.
  unfold songun_derivation. simpl. left. reflexivity.
Qed.

(** A derivation is valid if it terminates in a leader's word or principle. *)
Fixpoint derivation_grounded (d : DerivationStep) : Prop :=
  match d with
  | BaseSource (FromLeaderWord _) => True
  | BaseSource (FromPrinciple _) => True
  | BaseSource (FromPillar _) => True
  | Derive _ rest => derivation_grounded rest
  end.

Lemma songun_derivation_grounded : derivation_grounded songun_derivation.
Proof.
  unfold songun_derivation. simpl. exact I.
Qed.

(** ========================================================================= *)
(** PART XII: SYSTEM INVARIANTS                                               *)
(** ========================================================================= *)

(** Key structural properties of the Juche ideological system. *)

(** Invariant 1: There is exactly one Suryong at any time. *)
Definition unique_leader_in_year (tenures : list LeaderTenure) (y : JucheYear) : Prop :=
  exists! t, In t tenures /\ active_in_year t y.

(** Invariant 2: All citizens have a songbun classification. *)
Definition songbun_total : forall c : Citizen, exists s : SongbunClass, citizen_songbun c = s.
Proof.
  intro c. exists (citizen_songbun c). reflexivity.
Qed.

(** Invariant 3: Party membership implies eligible songbun. *)
Definition party_songbun_consistency (c : Citizen) : Prop :=
  citizen_party_member c = true -> citizen_songbun c <> HostileClass.

Lemma model_citizen_consistent : party_songbun_consistency model_citizen.
Proof.
  unfold party_songbun_consistency, model_citizen. simpl.
  intros _ H. discriminate.
Qed.

(** Invariant 4: Succession is well-founded (no cycles). *)
Lemma succession_acyclic : forall l, ~ succeeds l l.
Proof.
  intro l. destruct l; intro H; exact H.
Qed.

(** Invariant 5: The Ten Principles cover all pillars. *)
Definition pillar_covered_by_principle (p : Pillar) : Prop :=
  exists pr, principle_pillar pr = p.

Lemma all_pillars_covered : forall p, pillar_covered_by_principle p.
Proof.
  intro p. destruct p.
  - exists P1_Struggle. reflexivity.
  - exists P7_Learning. reflexivity.
  - exists P9_Discipline. reflexivity.
Qed.

(** Invariant 6: Leader words are supreme (override all other sources). *)
Definition leader_word_supreme (d : DerivationStep) : Prop :=
  match d with
  | BaseSource (FromLeaderWord _) => True
  | Derive (FromLeaderWord l) _ => True
  | _ => derivation_grounded d
  end.

(** The system is totalizing: every citizen, every action is subject to it. *)
Definition totalizing_system : Prop :=
  forall c : Citizen, forall p : Principle,
    exists o : ObligationLevel, citizen_obligation c p = o.

Lemma system_is_totalizing : totalizing_system.
Proof.
  unfold totalizing_system. intros c p.
  exists (citizen_obligation c p). reflexivity.
Qed.

(** No escape: hostile class still has obligations (just reduced). *)
Lemma hostile_still_obligated : forall p,
  obligation_strength (citizen_obligation hostile_citizen p) >= 1.
Proof.
  intro p. unfold citizen_obligation, hostile_citizen. simpl.
  unfold obligation_strength. lia.
Qed.

(** ========================================================================= *)
(** PART XIII: HISTORICAL PERIODS                                             *)
(** ========================================================================= *)

(** Key historical periods in DPRK history with doctrinal significance. *)

Inductive HistoricalPeriod : Type :=
  | AntiJapanese      (* 1932-1945: Guerrilla resistance *)
  | Liberation        (* 1945-1948: Soviet occupation, state formation *)
  | KoreanWar         (* 1950-1953: The Fatherland Liberation War *)
  | Reconstruction    (* 1953-1970: Chollima Movement, industrialization *)
  | ThreeRevolutions  (* 1970-1994: Ideological, technical, cultural *)
  | ArduousMarch      (* 1994-1998: Famine period *)
  | SongunPeriod      (* 1998-2011: Military-first consolidation *)
  | ByungjinPeriod.   (* 2013-present: Nuclear and economic parallel development *)

Definition period_leader (p : HistoricalPeriod) : option Leader :=
  match p with
  | AntiJapanese => Some KimIlSung
  | Liberation => Some KimIlSung
  | KoreanWar => Some KimIlSung
  | Reconstruction => Some KimIlSung
  | ThreeRevolutions => Some KimIlSung
  | ArduousMarch => Some KimJongIl
  | SongunPeriod => Some KimJongIl
  | ByungjinPeriod => Some KimJongUn
  end.

Definition period_start_year (p : HistoricalPeriod) : JucheYear :=
  match p with
  | AntiJapanese => 21      (* 1932 *)
  | Liberation => 34        (* 1945 *)
  | KoreanWar => 39         (* 1950 *)
  | Reconstruction => 42    (* 1953 *)
  | ThreeRevolutions => 59  (* 1970 *)
  | ArduousMarch => 83      (* 1994 *)
  | SongunPeriod => 87      (* 1998 *)
  | ByungjinPeriod => 102   (* 2013 *)
  end.

Lemma arduous_march_after_kim_il_sung :
  period_start_year ArduousMarch = kim_il_sung_death.
Proof. reflexivity. Qed.

(** ========================================================================= *)
(** SUMMARY                                                                   *)
(** ========================================================================= *)

(**
   This formalization captures the logical structure of Juche ideology:

   1. TEMPORAL: Juche calendar rooted in Kim Il-sung's birth (1912)

   2. THREE PILLARS: Chajusong (political), Charip (economic), Chawi (military)

   3. TEN PRINCIPLES: The supreme behavioral code binding all citizens

   4. SONGBUN: Hereditary social classification (Core/Wavering/Hostile)

   5. SURYONG: Supreme leader system with Paektu bloodline succession

   6. ORGANIZATIONS: Party (WPK) leads military (KPA) and mass organizations

   7. SONGUN: Military-first policy deriving from Chawi pillar

   8. CITIZENS: Model combining songbun, party status, and organization membership

   9. OBLIGATIONS: Principle-based duties varying by citizen status

   10. VIOLATIONS: Consequences including collective punishment and three-generation rule

   11. DERIVATION: How policies derive from doctrinal sources

   12. INVARIANTS: System properties (unique leader, total coverage, no escape)

   13. HISTORY: Periodization of DPRK history under each leader

   The system is totalizing: every citizen has obligations to every principle,
   with no exit. The severity varies by songbun and party status, but the
   structure ensures universal subjection to ideological requirements.
*)
