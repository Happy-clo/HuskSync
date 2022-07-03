package net.william278.husksync.player;

import de.themoep.minedown.MineDown;
import net.md_5.bungee.api.ChatMessageType;
import net.william278.husksync.BukkitHuskSync;
import net.william278.husksync.data.*;
import org.apache.commons.lang.ArrayUtils;
import org.bukkit.*;
import org.bukkit.advancement.Advancement;
import org.bukkit.advancement.AdvancementProgress;
import org.bukkit.attribute.Attribute;
import org.bukkit.entity.EntityType;
import org.bukkit.entity.Player;
import org.bukkit.event.player.PlayerTeleportEvent;
import org.bukkit.persistence.PersistentDataContainer;
import org.bukkit.persistence.PersistentDataType;
import org.bukkit.potion.PotionEffect;
import org.bukkit.potion.PotionEffectType;
import org.jetbrains.annotations.NotNull;

import java.util.*;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/**
 * Bukkit implementation of an {@link OnlineUser}
 */
public class BukkitPlayer extends OnlineUser {

    private static final HashMap<UUID, BukkitPlayer> cachedPlayers = new HashMap<>();
    private final Player player;

    private BukkitPlayer(@NotNull Player player) {
        super(player.getUniqueId(), player.getName());
        this.player = player;
    }

    public static BukkitPlayer adapt(@NotNull Player player) {
        if (cachedPlayers.containsKey(player.getUniqueId())) {
            return cachedPlayers.get(player.getUniqueId());
        }
        final BukkitPlayer bukkitPlayer = new BukkitPlayer(player);
        cachedPlayers.put(player.getUniqueId(), bukkitPlayer);
        return bukkitPlayer;
    }

    public static void remove(@NotNull Player player) {
        cachedPlayers.remove(player.getUniqueId());
    }

    @Override
    public CompletableFuture<StatusData> getStatus() {
        return CompletableFuture.supplyAsync(() -> {
            final double maxHealth = getMaxHealth(player);
            return new StatusData(Math.min(player.getHealth(), maxHealth),
                    maxHealth,
                    player.isHealthScaled() ? player.getHealthScale() : 0d,
                    player.getFoodLevel(),
                    player.getSaturation(),
                    player.getExhaustion(),
                    player.getInventory().getHeldItemSlot(),
                    player.getTotalExperience(),
                    player.getLevel(),
                    player.getExp(),
                    player.getGameMode().name(),
                    player.getAllowFlight() && player.isFlying());
        });
    }

    @Override
    public CompletableFuture<Void> setStatus(@NotNull StatusData statusData,
                                             boolean setHealth, boolean setMaxHealth,
                                             boolean setHunger, boolean setExperience,
                                             boolean setGameMode, boolean setFlying) {
        return CompletableFuture.runAsync(() -> {
            double currentMaxHealth = Objects.requireNonNull(player.getAttribute(Attribute.GENERIC_MAX_HEALTH))
                    .getBaseValue();
            if (setMaxHealth) {
                if (statusData.maxHealth != 0d) {
                    Objects.requireNonNull(player.getAttribute(Attribute.GENERIC_MAX_HEALTH))
                            .setBaseValue(statusData.maxHealth);
                    currentMaxHealth = statusData.maxHealth;
                }
            }
            if (setHealth) {
                final double currentHealth = player.getHealth();
                if (statusData.health != currentHealth) {
                    player.setHealth(currentHealth > currentMaxHealth ? currentMaxHealth : statusData.health);
                }

                if (statusData.healthScale != 0d) {
                    player.setHealthScale(statusData.healthScale);
                } else {
                    player.setHealthScale(statusData.maxHealth);
                }
                player.setHealthScaled(statusData.healthScale != 0D);
            }
            if (setHunger) {
                player.setFoodLevel(statusData.hunger);
                player.setSaturation(statusData.saturation);
                player.setExhaustion(statusData.saturationExhaustion);
            }
            if (setExperience) {
                player.setTotalExperience(statusData.totalExperience);
                player.setLevel(statusData.expLevel);
                player.setExp(statusData.expProgress);
            }
            if (setGameMode) {
                player.setGameMode(GameMode.valueOf(statusData.gameMode));
            }
            if (setFlying) {
                if (statusData.isFlying) {
                    player.setAllowFlight(true);
                    player.setFlying(true);
                }
                player.setFlying(false);
            }
        });
    }

    @Override
    public CompletableFuture<InventoryData> getInventory() {
        return BukkitSerializer.serializeInventory(player.getInventory().getContents())
                .thenApply(InventoryData::new);
    }

    @Override
    public CompletableFuture<Void> setInventory(@NotNull InventoryData inventoryData) {
        return BukkitSerializer.deserializeInventory(inventoryData.serializedInventory).thenAccept(contents ->
                Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(),
                        () -> player.getInventory().setContents(contents)));
    }

    @Override
    public CompletableFuture<InventoryData> getEnderChest() {
        return BukkitSerializer.serializeInventory(player.getEnderChest().getContents())
                .thenApply(InventoryData::new);
    }

    @Override
    public CompletableFuture<Void> setEnderChest(@NotNull InventoryData enderChestData) {
        return BukkitSerializer.deserializeInventory(enderChestData.serializedInventory).thenAccept(contents ->
                Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(),
                        () -> player.getEnderChest().setContents(contents)));
    }

    @Override
    public CompletableFuture<PotionEffectData> getPotionEffects() {
        return BukkitSerializer.serializePotionEffects(player.getActivePotionEffects()
                .toArray(new PotionEffect[0])).thenApply(PotionEffectData::new);
    }

    @Override
    public CompletableFuture<Void> setPotionEffects(@NotNull PotionEffectData potionEffectData) {
        return BukkitSerializer.deserializePotionEffects(potionEffectData.serializedPotionEffects).thenAccept(
                effects -> Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(), () -> {
                    for (PotionEffect effect : player.getActivePotionEffects()) {
                        player.removePotionEffect(effect.getType());
                    }
                    for (PotionEffect effect : effects) {
                        player.addPotionEffect(effect);
                    }
                }));
    }

    @Override
    public CompletableFuture<List<AdvancementData>> getAdvancements() {
        return CompletableFuture.supplyAsync(() -> {
            final Iterator<Advancement> serverAdvancements = Bukkit.getServer().advancementIterator();
            final ArrayList<AdvancementData> advancementData = new ArrayList<>();

            // Iterate through the server advancement set and add all advancements to the list
            serverAdvancements.forEachRemaining(advancement -> {
                final AdvancementProgress advancementProgress = player.getAdvancementProgress(advancement);
                final Map<String, Date> awardedCriteria = new HashMap<>();

                advancementProgress.getAwardedCriteria().forEach(criteriaKey -> awardedCriteria.put(criteriaKey,
                        advancementProgress.getDateAwarded(criteriaKey)));

                // Only save the advancement if criteria has been completed
                if (!awardedCriteria.isEmpty()) {
                    advancementData.add(new AdvancementData(advancement.getKey().toString(), awardedCriteria));
                }
            });
            return advancementData;
        });
    }

    @Override
    public CompletableFuture<Void> setAdvancements(@NotNull List<AdvancementData> advancementData) {
        return CompletableFuture.runAsync(() -> {
            // Temporarily disable advancement announcing if needed
            boolean announceAdvancementUpdate = false;
            if (Boolean.TRUE.equals(player.getWorld().getGameRuleValue(GameRule.ANNOUNCE_ADVANCEMENTS))) {
                player.getWorld().setGameRule(GameRule.ANNOUNCE_ADVANCEMENTS, false);
                announceAdvancementUpdate = true;
            }
            final boolean finalAnnounceAdvancementUpdate = announceAdvancementUpdate;

            // Save current experience and level
            final int experienceLevel = player.getLevel();
            final float expProgress = player.getExp();

            // Determines whether the experience might have changed warranting an update
            final AtomicBoolean correctExperience = new AtomicBoolean(false);

            // Apply the advancements to the player
            final Iterator<Advancement> serverAdvancements = Bukkit.getServer().advancementIterator();
            while (serverAdvancements.hasNext()) {
                // Iterate through all advancements
                final Advancement advancement = serverAdvancements.next();
                final AdvancementProgress playerProgress = player.getAdvancementProgress(advancement);

                advancementData.stream().filter(record -> record.key.equals(advancement.getKey().toString())).findFirst().ifPresentOrElse(
                        // Award all criteria that the player does not have that they do on the cache
                        record -> {
                            record.completedCriteria.keySet().stream()
                                    .filter(criterion -> !playerProgress.getAwardedCriteria().contains(criterion))
                                    .forEach(criterion -> {
                                        Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(),
                                                () -> player.getAdvancementProgress(advancement).awardCriteria(criterion));
                                        correctExperience.set(true);
                                    });

                            // Revoke all criteria that the player does have but should not
                            new ArrayList<>(playerProgress.getAwardedCriteria()).stream().filter(criterion -> !record.completedCriteria.containsKey(criterion))
                                    .forEach(criterion -> Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(),
                                            () -> player.getAdvancementProgress(advancement).revokeCriteria(criterion)));

                        },
                        // Revoke the criteria as the player shouldn't have any
                        () -> new ArrayList<>(playerProgress.getAwardedCriteria()).forEach(criterion ->
                                Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(),
                                        () -> player.getAdvancementProgress(advancement).revokeCriteria(criterion))));

                // Update the player's experience in case the advancement changed that
                if (correctExperience.get()) {
                    player.setLevel(experienceLevel);
                    player.setExp(expProgress);
                    correctExperience.set(false);
                }
            }

            // Re-enable announcing advancements (back on main thread again)
            Bukkit.getScheduler().runTask(BukkitHuskSync.getInstance(), () -> {
                if (finalAnnounceAdvancementUpdate) {
                    player.getWorld().setGameRule(GameRule.ANNOUNCE_ADVANCEMENTS, true);
                }
            });
        });
    }

    @Override
    public CompletableFuture<StatisticsData> getStatistics() {
        return CompletableFuture.supplyAsync(() -> {
            final Map<String, Integer> untypedStatisticValues = new HashMap<>();
            final Map<String, Map<String, Integer>> blockStatisticValues = new HashMap<>();
            final Map<String, Map<String, Integer>> itemStatisticValues = new HashMap<>();
            final Map<String, Map<String, Integer>> entityStatisticValues = new HashMap<>();

            for (Statistic statistic : Statistic.values()) {
                switch (statistic.getType()) {
                    case ITEM -> {
                        final Map<String, Integer> itemValues = new HashMap<>();
                        Arrays.stream(Material.values()).filter(Material::isItem)
                                .filter(itemMaterial -> (player.getStatistic(statistic, itemMaterial)) != 0)
                                .forEach(itemMaterial -> itemValues.put(itemMaterial.name(),
                                        player.getStatistic(statistic, itemMaterial)));
                        if (!itemValues.isEmpty()) {
                            itemStatisticValues.put(statistic.name(), itemValues);
                        }
                    }
                    case BLOCK -> {
                        final Map<String, Integer> blockValues = new HashMap<>();
                        Arrays.stream(Material.values()).filter(Material::isBlock)
                                .filter(blockMaterial -> (player.getStatistic(statistic, blockMaterial)) != 0)
                                .forEach(blockMaterial -> blockValues.put(blockMaterial.name(),
                                        player.getStatistic(statistic, blockMaterial)));
                        if (!blockValues.isEmpty()) {
                            blockStatisticValues.put(statistic.name(), blockValues);
                        }
                    }
                    case ENTITY -> {
                        final Map<String, Integer> entityValues = new HashMap<>();
                        Arrays.stream(EntityType.values()).filter(EntityType::isAlive)
                                .filter(entityType -> (player.getStatistic(statistic, entityType)) != 0)
                                .forEach(entityType -> entityValues.put(entityType.name(),
                                        player.getStatistic(statistic, entityType)));
                        if (!entityValues.isEmpty()) {
                            entityStatisticValues.put(statistic.name(), entityValues);
                        }
                    }
                    case UNTYPED -> {
                        if (player.getStatistic(statistic) != 0) {
                            untypedStatisticValues.put(statistic.name(), player.getStatistic(statistic));
                        }
                    }
                }
            }

            return new StatisticsData(untypedStatisticValues, blockStatisticValues,
                    itemStatisticValues, entityStatisticValues);
        });
    }

    @Override
    public CompletableFuture<Void> setStatistics(@NotNull StatisticsData statisticsData) {
        return CompletableFuture.runAsync(() -> {
            // Set untyped statistics
            for (String statistic : statisticsData.untypedStatistic.keySet()) {
                player.setStatistic(Statistic.valueOf(statistic), statisticsData.untypedStatistic.get(statistic));
            }

            // Set block statistics
            for (String statistic : statisticsData.blockStatistics.keySet()) {
                for (String blockMaterial : statisticsData.blockStatistics.get(statistic).keySet()) {
                    player.setStatistic(Statistic.valueOf(statistic), Material.valueOf(blockMaterial),
                            statisticsData.blockStatistics.get(statistic).get(blockMaterial));
                }
            }

            // Set item statistics
            for (String statistic : statisticsData.itemStatistics.keySet()) {
                for (String itemMaterial : statisticsData.itemStatistics.get(statistic).keySet()) {
                    player.setStatistic(Statistic.valueOf(statistic), Material.valueOf(itemMaterial),
                            statisticsData.itemStatistics.get(statistic).get(itemMaterial));
                }
            }

            // Set entity statistics
            for (String statistic : statisticsData.entityStatistics.keySet()) {
                for (String entityType : statisticsData.entityStatistics.get(statistic).keySet()) {
                    player.setStatistic(Statistic.valueOf(statistic), EntityType.valueOf(entityType),
                            statisticsData.entityStatistics.get(statistic).get(entityType));
                }
            }
        });
    }

    @Override
    public CompletableFuture<LocationData> getLocation() {
        return CompletableFuture.supplyAsync(() ->
                new LocationData(player.getWorld().getName(), player.getWorld().getUID(), player.getWorld().getEnvironment().name(),
                        player.getLocation().getX(), player.getLocation().getY(), player.getLocation().getZ(),
                        player.getLocation().getYaw(), player.getLocation().getPitch()));
    }

    @Override
    public CompletableFuture<Void> setLocation(@NotNull LocationData locationData) {
        final CompletableFuture<Void> completableFuture = new CompletableFuture<>();
        AtomicReference<World> bukkitWorld = new AtomicReference<>(Bukkit.getWorld(locationData.worldName));
        if (bukkitWorld.get() == null) {
            bukkitWorld.set(Bukkit.getWorld(locationData.worldUuid));
        }
        if (bukkitWorld.get() == null) {
            Bukkit.getWorlds().stream().filter(world -> world.getEnvironment() == World.Environment
                    .valueOf(locationData.worldEnvironment)).findFirst().ifPresent(bukkitWorld::set);
        }
        if (bukkitWorld.get() != null) {
            player.teleport(new Location(bukkitWorld.get(),
                    locationData.x, locationData.y, locationData.z,
                    locationData.yaw, locationData.pitch), PlayerTeleportEvent.TeleportCause.PLUGIN);
        }
        CompletableFuture.runAsync(() -> completableFuture.completeAsync(() -> null));
        return completableFuture;
    }

    @Override
    public CompletableFuture<PersistentDataContainerData> getPersistentDataContainer() {
        return CompletableFuture.supplyAsync(() -> {
            final PersistentDataContainer container = player.getPersistentDataContainer();
            if (container.isEmpty()) {
                return new PersistentDataContainerData(new HashMap<>());
            }
            final HashMap<String, Byte[]> persistentDataMap = new HashMap<>();
            for (NamespacedKey key : container.getKeys()) {
                persistentDataMap.put(key.toString(), ArrayUtils.toObject(container.get(key, PersistentDataType.BYTE_ARRAY)));
            }
            return new PersistentDataContainerData(persistentDataMap);
        });
    }

    @Override
    public CompletableFuture<Void> setPersistentDataContainer(@NotNull PersistentDataContainerData persistentDataContainerData) {
        return CompletableFuture.runAsync(() -> {
            player.getPersistentDataContainer().getKeys().forEach(namespacedKey ->
                    player.getPersistentDataContainer().remove(namespacedKey));
            persistentDataContainerData.persistentDataMap.keySet().forEach(keyString -> {
                final NamespacedKey key = NamespacedKey.fromString(keyString);
                if (key != null) {
                    final byte[] data = ArrayUtils.toPrimitive(persistentDataContainerData
                            .persistentDataMap.get(keyString));
                    player.getPersistentDataContainer().set(key, PersistentDataType.BYTE_ARRAY, data);
                }
            });
        });
    }

    @Override
    public boolean hasPermission(@NotNull String node) {
        return player.hasPermission(node);
    }

    @Override
    public void sendActionBar(@NotNull MineDown mineDown) {
        player.spigot().sendMessage(ChatMessageType.ACTION_BAR, mineDown.toComponent());
    }

    @Override
    public void sendMessage(@NotNull MineDown mineDown) {
        player.spigot().sendMessage(mineDown.toComponent());
    }

    /**
     * Returns a {@link Player}'s maximum health, minus any health boost effects
     *
     * @param player The {@link Player} to get the maximum health of
     * @return The {@link Player}'s max health
     */
    private static double getMaxHealth(@NotNull Player player) {
        double maxHealth = Objects.requireNonNull(player.getAttribute(Attribute.GENERIC_MAX_HEALTH)).getBaseValue();

        // If the player has additional health bonuses from synchronised potion effects, subtract these from this number as they are synchronised separately
        if (player.hasPotionEffect(PotionEffectType.HEALTH_BOOST) && maxHealth > 20D) {
            PotionEffect healthBoostEffect = player.getPotionEffect(PotionEffectType.HEALTH_BOOST);
            assert healthBoostEffect != null;
            double healthBoostBonus = 4 * (healthBoostEffect.getAmplifier() + 1);
            maxHealth -= healthBoostBonus;
        }
        return maxHealth;
    }

}
