use oxrdf::NamedNodeRef;

pub const VERIFIABLE_CREDENTIAL_TYPE: NamedNodeRef =
    NamedNodeRef::new_unchecked("https://www.w3.org/2018/credentials#VerifiableCredential");
pub const PROOF: NamedNodeRef = NamedNodeRef::new_unchecked("https://w3id.org/security#proof");
