use newtype_macros::{wrap_string, wrap_u128, wrap_u64};

wrap_string!(Asset);

wrap_string!(Channel);

wrap_string!(Address);

wrap_u128!(Deposits);

wrap_u64!(Cooldown);

mod state {
    use cw_storage_macros::{composite_key, example_key, item, map};

    use crate::{Address, Asset, Channel, Cooldown, Deposits};

    item!(name           : String);
    item!(connection_id! : String);
    item!(asset          : Asset    as String);
    item!(channel!       : Channel  as String);
    item!(count          : u64);
    item!(fee_bps!       : u32);
    item!(deposits       : Deposits as u128);
    item!(cooldown!      : Cooldown as u64);

    // Tests generated in macro don't know how to construct key types, this helps them.
    // TODO: Remove the need for this
    example_key!(Address, "xyz");
    example_key!(Channel, "test");

    composite_key!(CompositeKey, from: (Address, Channel));

    map!(address: Address              => name         : String);
    map!(source: String                => destination! : String);
    map!(idx: u64                      => address      : Address  as String);
    map!(idx: u64                      => channel!     : Channel  as String);
    map!(idx: u64                      => count        : u64);
    map!(idx: u64                      => fee_bps!     : u32);
    map!(idx: u64                      => deposits     : Deposits as u128);
    map!(idx: u64                      => cooldown!    : Cooldown as u64);
    map!(address_channel: CompositeKey => cooldown!    : Cooldown as u64);
}

#[test]
#[should_panic(expected = "idx_cooldown always set")]
fn generated_api() {
    let mut storage = cosmwasm_std::testing::MockStorage::default();

    state::set_name(&mut storage, "alice");

    assert_eq!(state::name(&storage), Some("alice".to_owned()));

    state::clear_name(&mut storage);

    assert_eq!(state::name(&storage), None);

    state::set_cooldown(&mut storage, Cooldown::from(1000));

    // Assumes that cooldown has been previously set and panics if it hasn't.
    // Useful for configuration that is set in instantiate handlers.
    assert_eq!(state::cooldown(&storage), Cooldown::from(1000));

    assert_eq!(state::idx_deposits(&storage, 0), None);

    state::set_idx_deposits(&mut storage, 0, Deposits::from(1_000_000));

    assert_eq!(
        state::idx_deposits(&storage, 0),
        Some(Deposits::from(1_000_000))
    );

    state::clear_idx_deposits(&mut storage, 0);

    assert_eq!(state::idx_deposits(&storage, 0), None);

    state::set_idx_fee_bps(&mut storage, 1, 1_000);

    assert_eq!(state::idx_fee_bps(&storage, 1), 1_000);

    // this will panic because it a cooldown has not been set for index 2
    state::idx_cooldown(&storage, 2);
}
