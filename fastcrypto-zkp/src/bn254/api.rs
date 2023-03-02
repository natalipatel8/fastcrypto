// // Copyright (c) 2022, Mysten Labs, Inc.
// // SPDX-License-Identifier: Apache-2.0
//
// use ark_bn254::{Bn254, Fr};
// use ark_groth16::{Proof, VerifyingKey};
// use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
// use fastcrypto::error::FastCryptoError;
// use crate::bn254::verifier::{PreparedVerifyingKey, process_vk, verify_with_processed_vk};
//
// #[cfg(test)]
// #[path = "unit_tests/api_tests.rs"]
// mod api_tests;
//
// /// Deserialize bytes as an Arkwork representation of a verifying key, and return a vector of the four components of a prepared verified key (see more at [`crate::verifier::PreparedVerifyingKey`]).
// pub fn prepare_pvk_bytes(vk_bytes: &[u8]) -> Result<Vec<Vec<u8>>, FastCryptoError> {
//     let vk = VerifyingKey::<Bn254>::deserialize(vk_bytes)
//         .map_err(|_| FastCryptoError::InvalidInput)?;
//     process_vk(&vk)?.as_serialized()
// }
//
// /// Verify Groth16 proof using the serialized form of the four components in a prepared verifying key
// /// (see more at [`crate::verifier::PreparedVerifyingKey`]), serialized proof public input and serialized proof points.
// pub fn verify_groth16_in_bytes(
//     vk_gamma_abc_g1_bytes: &[u8],
//     alpha_g1_beta_g2_bytes: &[u8],
//     gamma_g2_neg_pc_bytes: &[u8],
//     delta_g2_neg_pc_bytes: &[u8],
//     proof_public_inputs_as_bytes: &[u8],
//     proof_points_as_bytes: &[u8],
// ) -> Result<bool, FastCryptoError> {
//
//     let mut x = Vec::new();
//     for chunk in proof_public_inputs_as_bytes.chunks(32) {
//         if chunk.len() != 32 {
//             return Err(FastCryptoError::InputLengthWrong(32));
//         }
//         x.push(Fr::deserialize(chunk).map_err(|_| FastCryptoError::InvalidInput)?);
//     }
//     let proof = Proof::<Bn254>::deserialize(proof_points_as_bytes)
//         .map_err(|_| FastCryptoError::InvalidInput)?;
//
//     let blst_pvk = PreparedVerifyingKey::deserialize(
//         vk_gamma_abc_g1_bytes,
//         alpha_g1_beta_g2_bytes,
//         gamma_g2_neg_pc_bytes,
//         delta_g2_neg_pc_bytes,
//     )?;
//
//     verify_with_processed_vk(&blst_pvk, &x, &proof)
//         .map_err(|_| FastCryptoError::GeneralOpaqueError)
// }
